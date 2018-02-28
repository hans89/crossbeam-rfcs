# Summary

This RFC proposes an implementation of dynamic-sized circular **half-stealing** double-ended queue
(deque) on Crossbeam, and its correctness proof. this RFC has a [companion PR to
`crossbeam-deque`][deque-pr]. This RFC shares a lot of details with the [deque-proof
RFC][deque-proof-rfc], which proves the correctness of deque. So we focus on the changes we made for
`steal_half()`, while making sure that this RFC is self-contained.



# Motivation

The current implementation of deque provides the `steal()` method for stealers, which steals only
one work at a time. But in some use cases, it is desirable to steal more works at once for evenly
distributing works across multiple threads (see [this paper][steal-half] for more details). This RFC
proposes a dynamic-sized circular half-stealing deque, which provides the `steal_half()` method that
steals half of all the works in a deque. In addition, for ensuring its correctness, we prove the
proposed deque's linearizability.



# Detailed design

In this section, we present a pseudocode of deque with the `steal_half()` method, and prove that (1)
it is safe in the C/C++ memory consistency model, and (2) it is functionally correct, i.e. it acts
like a half-stealing deque.


## Proposed implementation

In this section, we present a pseudocode of deque, and prove that (1) it is safe in the C/C++ memory
consistency model, and (2) it is functionally correct, i.e. it acts like a deque.


## Semantics of C/C++ relaxed-memory concurrency

Note that this subsection is copy-and-pasted from the [deque-proof RFC][deque-proof-rfc].

For the semantics of C/C++ relaxed-memory concurrency on which the deque implementation is based, we
use the state-of-the-art [promising semantics][promising]. For a gentle introduction to the
semantics, we refer the reader to [this blog post][synch-patterns].

One caveat of the original promising semantics is its lack of support for memory allocation. In this
RFC, we use the following semantics for memory allocation:

- In the original promising semantics, a timestamp was a non-negative quotient number: `Timestamp =
  Q+`. Now we define `Timestamp = Option<Q+>`, where `None` means the location is unallocated.
  Suppose `None < Some(t)` for all `t`.

- At the beginning, a thread's view is `None` for all the locations. When a thread allocates a
  location, its view on the location becomes `0`.

- If a thread is reading a location and it's view on the location is `None`, i.e. it is unallocated
  in the thread's point of view, then the behavior is undefined.

We believe this definition is compatible with all the results presented in the [the promising
semantics paper][promising]. We hope [its Coq formalization][promising-coq] be updated accordingly
soon.


## Proposed implementation

As before, a half-stealing deque is owned by the "owner" thread (`Deque<T>`), which can push items
to and pop items from the "bottom" end of the deque. Other threads, which we call "stealers"
(`Stealer<T>`), try to steal items from the "top" end of the deque. The following is a summary of
its interface:

```rust
impl<T: Send> Deque<T> { // Send + !Sync
    pub fn new() -> Self { ... }
    pub fn stealer(&self) -> Stealer<T> { ... }

    pub fn push(&self, value: T) { ... }
    pub fn pop(&self) -> Option<T> { ... } // None if empty
}

impl<T: Send> Stealer<T> { // Send + Sync + Clone
    pub fn steal(&self) -> Option<T> { ... }
    pub fn steal_half(&self) -> Option<Vec<T>> { ... }
}
```

Chase and Lev proposed [an efficient implementation of deque][chase-lev] on sequentially consistent
memory model, and Lê et. al. proposed [its variant for ARM and C/C++ relaxed-memory
concurrency][chase-lev-weak]. This RFC presents an even more optimized variant for C/C++.

A Chase-Lev deque consists of (1) the `bottom` index for the owner, (2) the `top` index for both the
owner and the stealers, and (3) the underlying `buffer` that contains items, and (4) `max_bottom`,
which is first introduced in this RFC, that stores the maximum value of `bottom` after the owner
made a consensus using a CAS for the last time. When the buffer is too small or too large, the owner
may replace it with one with more appropriate size:

```rust
struct<T: Send> Inner<T> {
    bottom: AtomicUsize,
    top: AtomicUsize,
    buffer: Ptr<Buffer<T>>,
    max_bottom: AtomicUsize, // new
}

impl<T: Send> Inner<T> {
    ...
}
```

The `Deque` and `Stealer` structs have a counted reference to the inner implementation, and delegate
method invocations to it:

```rust
struct<T: Send> Deque<T> {
    inner: Arc<Inner<T>>,
}

impl<T:Send> Deque<T> {
    fn push(...) {
        self.inner.push(...)
    }

    ...
}

...
```

The pseudocode for `Inner<T>`'s `fn push()`, `fn pop()`, `fn steal()`, and `fn steal_half()` is as
follows:

```rust
pub fn push(&self, value: T) {
    'L101: let b = self.bottom.load(Relaxed);
    'L102: let t = self.top.load(Acquire);
    'L103: let mut buffer = self.buffer.load(Relaxed, epoch::unprotected());

    'L104: let cap = buffer.get_capacity();
    'L105: if b - t >= cap {
    'L106:     self.resize(cap * 2);
    'L107:     buffer = self.buffer.load(Relaxed, epoch::unprotected());
    'L108: }

    'L109: buffer.write(b % buffer.get_capacity(), value, Relaxed);
    'L110: self.bottom.store(b + 1, Release);

    'N111: if self.max_bottom.get() < b + 1 { self.max_bottom.set(b + 1); }
}

pub fn pop(&self) -> Option<T> {
    'L201: let b = self.bottom.load(Relaxed);
    'L202: self.bottom.store(b - 1, Relaxed);
    'L203: fence(SeqCst);
    'N204: let buffer = self.buffer.load(Relaxed, epoch::unprotected());
    'N205: let mut t = self.top.load(Relaxed);
    'N206: let mut len = b - t;
    'N207: let max_steal = t + (self.max_bottom.get() - t + 1) / 2;

    'N207: {   while 2 <= len {
    if max_steal < b {
    'N208:     let let = b - t;
    'N209:     let cap = buffer.get_capacity();
    'N210:     if len < cap / 4 {
    'N211:         self.resize(cap / 2);
    'N212:     }
    'N213:     return Some(buffer.read(b - 1, Relaxed));
    'N214: }

    'N215: while t < b {
    'N216:     match self.top.compare_and_swap_weak(t, t + 1, Release, Relaxed) {
    'N217:         Ok(_) => {
    'N218:             self.bottom.store(b, Relaxed);
    'N219:             self.max_bottom.set(b);
    'N220:             return Some(buffer.read(t, Relaxed));
    'N221:         }
    'N222:         Err(t_cur) => t = t_cur,
    'N223:     }
    'N224: }

    'N225: fence(Acquire);
    'N226: self.bottom.store(b, Relaxed);
    'N227: None
}

fn resize(&self, cap_new) {
    'L301: let b = self.bottom.load(Relaxed);
    'L302: let t = self.top.load(Relaxed);
    'L303: let old = self.buffer.load(Relaxed, epoch::unprotected());
    'L304: let new = Buffer::new(cap_new);

    'L305: ... // copy data from old to new

    'L306: let guard = epoch::pin();
    'L307: self.buffer.store(Owned::new(new).into_shared(guard), Release);
    'L308: guard.defer(move || old.into_owned());
}

pub fn steal(&self) -> Option<T> {
    'L401: let mut t = self.top.load(Relaxed);

    'L402: let guard = epoch::pin_fence(); // epoch::pin(), but issue fence(SeqCst) even if it is re-entering
    'L403: loop {
    'L404:     let b = self.bottom.load(Acquire);
    'L405:     if b - t <= 0 {
    'L406:         return None;
    'L407:     }

    'L408:     let buffer = self.buffer.load(Acquire, &guard);
    'L409:     let value = buffer.read(t % buffer.get_capacity(), Relaxed);

    'L410:     match self.top.compare_and_swap_weak(t, t + 1, Release) {
    'L411:         Ok(_) => return Some(value),
    'L412:         Err(t_old) => {
    'L413:             mem::forget(value);
    'L414:             t = t_old;
    'L415:             fence(SeqCst);
    'L416:         }
    'L417:     }
    'L418: }
}
```








- For reference, `steal()` is defined as follows:

  ```rust
  pub fn steal(&self) -> Option<T> {
      'L401: let mut t = self.top.load(Relaxed);

      'L402: let guard = epoch::pin_fence(); // epoch::pin(), but issue fence(SeqCst) even if it is re-entering
      'L403: loop {
      'L404:     let b = self.bottom.load(Acquire);
      'N405:     if b - t <= 0 { return None; } // 'L405-'L407

      'L408:     let buffer = self.buffer.load(Acquire, &guard);
      'L409:     let value = buffer.read(t % buffer.get_capacity(), Relaxed);

      'L410:     match self.top.compare_and_swap_weak(t, t + 1, Release) {
      'L411:         Ok(_) => return Some(value),
      'L412:         Err(t_old) => {
      'L413:             mem::forget(value);
      'L414:             t = t_old;
      'L415:             fence(SeqCst);
      'L416:         }
      'L417:     }
      'L418: }
  }
  ```

  Note that the lines whose label starts with `N` (e.g. `'N111`) are those lines introduced in this
  RFC; the other lines are introduced in the [deque-proof RFC][deque-proof-rfc]. Here, `'L405-'L407`
  is just written in the single line `'N405`.

- `steal_half()` is a straightforward generalization of `steal()` that steals half of the elements
  at once:

  ```rust
  pub fn steal_half(&self) -> Steal<Vec<T>> {
      'N501: let mut t = self.top.load(Relaxed);

      'N502: let guard = epoch::pin_fence(); // epoch::pin(), but issue fence(SeqCst) even if it is re-entering
      'N503: loop {
      'N504:     let b = self.bottom.load(Acquire);
      'N505:     if b - t <= 0 { return None; }

      'N506:     let max_steal = t + (b - t + 1) / 2;
      'N508:     let buffer = self.buffer.load(Acquire, &guard);
      'N509:     let values = buffer.read_range(t, max_steal, Relaxed);

      'N510:     match self.top.compare_and_swap_weak(t, max_steal, Release) {
      'N511:         Ok(_) => return Some(values),
      'N512:         Err(t_old) => {
      'N513:             mem::forget(values);
      'N514:             t = t_old;
      'N515:             fence(SeqCst);
      'N516:         }
      'N517:     }
      'N518: }
  }
  ```

  Here, `max_steal` is the mid-point of `t` and `b` (`'N506`), and `steal_half()` tries to steal the
  elements at `[t, max_steal)` and updates `top` to `max_steal`.  `steal_half()` is different from
  `steal()` only in `'N506` and `'N510`.

- In order for stealers to safely steal half of the elements, it is necessary for the owner to
  abstain from popping too many elements (i.e. below `max_steal` calculated in `steal_half()`). For
  example, consider a deque of 100 elements at `[0, 100)`. A stealer may read `top = 0` and `bottom
  = 100`, and then be preempted right after `'N504`. Concurrently, the worker may pop 60
  elements. Now the stealer may win the race in `'N509`, updating `top = 50` and stealing elements
  at `[0, 50)`. But this is incorrect: the elements at `[40, 50)` are already popped.

  For avoiding this scenario, the owner records the maximum value of `bottom` after its last
  successful steal (i.e. popping an element from the top end), which can be used to conservatively
  estimate `max_steal` calculated in concurrent `steal_half()` invocations:

  ```rust
  struct<T: Send> Inner<T> {
      bottom: AtomicUsize,
      top: AtomicUsize,
      buffer: Ptr<Buffer<T>>,
      max_bottom: Cell<isize>, // new
  }
  ```

  Note that in the companion implementation, `Deque<T>` has `max_bottom`, instead of `Inner<T>`. It
  is okay because `max_bottom` is accessed only by the worker.


- In order to maintain the up-to-date information, `push()` updates `max_bottom` if the new `bottom`
  is bigger than that:

  ```rust
  pub fn push(&self, value: T) {
      'L101: let b = self.bottom.load(Relaxed);
      'L102: let t = self.top.load(Acquire);
      'L103: let mut buffer = self.buffer.load(Relaxed, epoch::unprotected());

      'L104: let cap = buffer.get_capacity();
      'L105: if b - t >= cap {
      'L106:     self.resize(cap * 2);
      'L107:     buffer = self.buffer.load(Relaxed, epoch::unprotected());
      'L108: }

      'L109: buffer.write(b % buffer.get_capacity(), value, Relaxed);
      'L110: self.bottom.store(b + 1, Release);

      'N111: if self.max_bottom.get() < b + 1 { self.max_bottom.set(b + 1); }
  }
  ```


- Now `pop()` recognizes `max_bottom`, and estimates which elements are definitely not stolen by
  concurrent stealers and safe to pop. Using this information, it abstains from popping too many
  elements:

  ```rust
  pub fn pop(&self) -> Option<T> {
      'L201: let b = self.bottom.load(Relaxed);
      'L202: self.bottom.store(b - 1, Relaxed);
      'L203: fence(SeqCst);
      'N204: let buffer = self.buffer.load(Relaxed, epoch::unprotected());
      'N205: let mut t = self.top.load(Relaxed);
      'N206: let max_steal = t + (self.max_bottom.get() - t + 1) / 2;

      'N207: if max_steal < b {
      'N208:     let let = b - t;
      'N209:     let cap = buffer.get_capacity();
      'N210:     if len < cap / 4 {
      'N211:         self.resize(cap / 2);
      'N212:     }
      'N213:     return Some(buffer.read(b - 1, Relaxed));
      'N214: }

      'N215: while t < b {
      'N216:     match self.top.compare_and_swap_weak(t, t + 1, Release, Relaxed) {
      'N217:         Ok(_) => {
      'N218:             self.bottom.store(b, Relaxed);
      'N219:             self.max_bottom.set(b);
      'N220:             return Some(buffer.read(t, Relaxed));
      'N221:         }
      'N222:         Err(t_cur) => t = t_cur,
      'N223:     }
      'N224: }

      'N225: fence(Acquire);
      'N226: self.bottom.store(b, Relaxed);
      'N227: None
  }
  ```

  Provided that `max_steal < b`, it is safe to pop the last element at `b-1`(the "regular path",
  `'N207-'N214`). This is roughly because, thanks to seqcst-fences, a concurrent stealer should
  either (1) read from `bottom` a value `<= b-1`, or (2) read from `top` a value `<= t` and from
  `bottom` a value `<= max_bottom`. If the former is the case, it is obvious that the stealer cannot
  steal the element at `b-1`; if the latter is the case, the stealer can steal up-to the element at
  `max_steal = t + (b - t + 1) / 2` (`'N206`, also see `'N506`), leaving the element at `b-1`
  intact.

  Otherwise, `pop()` tries to steal the first element from the top end (the "irregular path",
  `'N215-'N227`). If successful, `max_bottom` is updated to the current value of `bottom`, since
  later stealers should recognize `pop()`'s write to `bottom` at `'L202`. As a side effect,
  **`pop()` no longer acts like a LIFO**: when it takes the irregular path, it may steal an element
  from the top end.

  If `b <= t`, then the deque is empty (`'N225-'N227`). As discussed in the [deque-proof
  RFC][deque-proof-rfc-optimal-orderings], the acquire-fence at `'N225` is necessary for linearizing
  `pop()` and `steal()` invocations returning `EMPTY`.



## Safety

The proposed half-stealing deque is safe for almost the same reason as discussed in the [deque-proof
RFC][deque-proof-rfc].


## Functional Correctness

The specification and the overall proof structure are similar to those in the [deque-proof
RFC][deque-proof-rfc].


## Specification

As in the [deque-proof RFC][deque-proof-rfc], the half-stealing deque satisfies linearizability and
synchronization properties. But as discussed above, the sequential specification of `pop()` is
changed: if `t < b`, then a `pop()` invocation either (1) decreases the bottom index `b` and pop the
last element, or (2) increases the top index `t` and steal the first element; otherwise, `pop()`
touches nothing and returns `EMPTY`.


## Construction of Linearization Order

The linearization order is constructed in the same way as before. Here, assume that a `steal_half()`
invocation that steals elements at `[x, y)` is in `STEAL^x`.

It is worth noting that the meaning of `pop()` taking the regular and the irregular paths are
changed as discussed above.

FIXME(jeehoonkang): skip irregular `pop()` only if top order is good..


## Auxiliary Definitions and Lemma

Suppose that `O_i` is `pop()` taking the irregular path, and `x` be the value `O_i` read from
`bottom` at `'L201`.

- The proof of `(IRREGULAR-TOP)` is changed as follows.

  Let `y` be the value `O_i` read from `top` at `'L205`. Since `O_i` is taking the irregular path,
  we have `x-1 <= y`. If `x <= y`, then the conclusion trivially follows. If `y = x-1`, then `O_i`
  tries to compare-and-swap (CAS) `top` from `x-1` to `x` at `'L213`. Regardless of whether the CAS
  succeeds or fails, `O_i` reads or writes `top >= x`.

  It is worth nothing that for this lemma to hold, it is necessary for the CAS at `'L213` to be
  strong, i.e. the CAS does not spuriously fail.








Also, the line numbers are a little bit changed, e.g. `'L210` in the [deque-proof
RFC][deque-proof-rfc] corresponds to `'N204` in this RFC.


The overall proof structure is the same as before. But as discussed above, the meaning of `pop()`
taking the regular and the irregular paths are changed. Also, the line numbers are a little bit
changed, e.g. `'L210` in the [deque-proof RFC][deque-proof-rfc] corresponds to `'N204` in this
RFC. We list up the changes we needed to make in the proof.




FIXME(jeehoonkang): TODO


## Proof of `(VIEW)`

FIXME(jeehoonkang): TODO


## Proof of `(SEQ)` and `(SYNC)`

FIXME(jeehoonkang): TODO



# Discussion

## Popping multiple elements

`pop()` can safely pop multiple elements at once as follows. First, `pop()` just decreases `bottom`
as much as it wants to pop at `'N202`. We know whether it is safe to pop such many elements from the
information gathered in `'N206`: the elements at `max_steal` and above are safe to pop. If not all
elements are safe to pop in `'N208-'N213`, `pop`() discards unsafe elements and return safe elements
only.

However, it's dubious whether this multi-popping scheme is practically useful. We leave the
investigation of its use cases as a future work.


## Stealing other-than-half elements

You may notice that `steal_half()` and `pop()` has _a priori_ agreement that a stealer may steal at
most half of the elements (`'N206` and `'N506`). It is possible to make a different agreement.
Roughly speaking, they may have agreed on a **steal bound function** `s(x)`, where `s(x)` is
increasing, `s(1) = 1`, and `s(x) < x` for `1 < x`, so that if the deque has `x` elements,
`steal_half()` may try to steal at most `s(x)` elements and `pop()` takes at most `x - s(x)`
elements from the bottom end.

The optimal steal bounds will be different for different applications. We leave the performance
evaluation of various configurations for various applications as a future work.


## Comparison to prior work

[Rudolph _et al_.][rudolph] and [Hendler _et al_.][steal-half] also proposed concurrent deques that
supports stealing multiple elements at once. However, these algorithms are neither dynamic-sized nor
circular. Furthermore, the workers in these algorithms perform CASes more often than the workers in
the algorithm proposed in this RFC. More precisely, [Rudolph _et al_.][rudolph]'s `push()` and
`pop()` always perform a CAS, and [Hendler _et al_.][steal-half]'s `pop()` should perform a CAS
whenever a stealer succeeded in stealing elements. On the other hand, our worker performs CAS
`O(log n)` times, where `n` is the total number of `pop()` operations. In essence, we could reduce
the number of CASes because we recorded `max_bottom`, instead of recording `max_steal` as [Hendler
_et al_.][steal-half] did.




[chase-lev]: https://pdfs.semanticscholar.org/3771/77bb82105c35e6e26ebad1698a20688473bd.pdf
[chase-lev-weak]: http://www.di.ens.fr/~zappa/readings/ppopp13.pdf
[fence-free-stealing]: http://www.cs.tau.ac.il/~mad/publications/asplos2014-ffwsq.pdf
[deque-current]: https://github.com/crossbeam-rs/crossbeam-deque
[deque-bounded-tso]: http://www.cs.tau.ac.il/~mad/publications/asplos2014-ffwsq.pdf
[deque-pr]: https://github.com/jeehoonkang/crossbeam-deque/tree/half-stealing
[deque-proof-rfc]: https://github.com/jeehoonkang/crossbeam-rfcs/blob/deque-proof/text/2018-01-07-deque-proof.md
[deque-proof-rfc-optimal-orderings]: https://github.com/jeehoonkang/crossbeam-rfcs/blob/deque-proof/text/2018-01-07-deque-proof.md#optimal-orderings
[rfc-relaxed-memory]: https://github.com/crossbeam-rs/rfcs/blob/master/text/2017-07-23-relaxed-memory.md
[promising]: http://sf.snu.ac.kr/promise-concurrency/
[promising-coq]: https://github.com/snu-sf/promising-coq
[synch-patterns]: https://jeehoonkang.github.io/2017/08/23/synchronization-patterns.html
[linearizability]: https://dl.acm.org/citation.cfm?id=78972
[cppatomic]: http://en.cppreference.com/w/cpp/atomic/atomic
[n3710]: http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2013/n3710.html
[c11]: www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf
[mp+dmb+ctrl]: https://www.cl.cam.ac.uk/~pes20/arm-supplemental/arm033.html
[arm-power]: https://www.cl.cam.ac.uk/~pes20/ppc-supplemental/test7.pdf
[steal-half]: https://www.cs.bgu.ac.il/~hendlerd/papers/p280-hendler.pdf
[rudolph]: http://people.csail.mit.edu/rudolph/Autobiography/LoadBalancing.pdf
