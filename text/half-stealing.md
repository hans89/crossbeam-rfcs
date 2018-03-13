  Here, `max_steal` is the mid-point of `t` and `b` (`'N506`), and `steal_half()` tries to steal the
  elements at `[t, max_steal)` and updates `top` to `max_steal`.  `steal_half()` is different from
  `steal()` only in `'N506` and `'N510`.

- For avoiding this scenario, the owner records the maximum value of `bottom` after its last
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
