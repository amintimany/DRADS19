From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare weakestpre.
From iris.heap_lang Require Import notation proofmode lifting adequacy.

Definition alloc_incr : expr :=
  (let: "x" := ref #0 in "x" <- !"x" + #1;; ! "x")%E.

Section alloc_incr.
  Context `{!heapG Σ}.

Theorem alloc_incr_spec :
  {{ True }} alloc_incr {{v, ⌜v = #1⌝ }}.
Proof.
  iAlways.
  iIntros "Hpre".
  unfold alloc_incr.
  About wp_alloc.
  wp_alloc l as "Hl".
  wp_let.
  About wp_load.
  wp_load.
  wp_op.
  wp_store.
  wp_load.
  trivial.
Qed.

End alloc_incr.

Print adequate.

Theorem alloc_incr_safety σ :
  adequate NotStuck alloc_incr σ (λ v _, v = #1).
  eapply (heap_adequacy heapΣ).
  iIntros (?).
  iApply alloc_incr_spec.
  trivial.
Qed.
