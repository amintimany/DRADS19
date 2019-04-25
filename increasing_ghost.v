From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import base_logic lib.own.

Class IncreasingG Σ :=
{
  IGT_inG :> inG Σ (authUR mnatUR);
}.

Section ghost_theory.
  Context `{IncreasingG Σ}.

  Definition Max γ (n : Z) : iProp Σ :=
    (⌜(0 ≤ n)%Z⌝ ∗ own γ (● (Z.to_nat n : mnat)))%I.

  Definition Seen γ (n : Z) : iProp Σ :=
    (⌜(0 ≤ n)%Z⌝ ∗ own γ (◯ (Z.to_nat n : mnat)))%I.

  Lemma IGT_alloc n : (0 ≤ n)%Z → (|==> ∃ γ, Max γ n)%I.
  Proof.
    iIntros (Hn).
    iMod (own_alloc (● (Z.to_nat n : mnat))) as (γ) "H".
    { by apply auth_auth_valid. }
    iModIntro. iExists γ.
    rewrite /Max; auto.
  Qed.

  Lemma Seen_le_Max γ n m : Max γ m -∗ Seen γ n -∗ ⌜(n ≤ m)%Z⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as "[% H1]".
    iDestruct "H2" as "[% H2]".
    iDestruct (own_valid_2 with "H1 H2") as %[? _]%auth_valid_discrete_2.
    iPureIntro.
    apply Z2Nat.inj_le; auto.
    by apply mnat_included.
  Qed.

  Lemma Observe γ n : Max γ n ==∗ Max γ n ∗ Seen γ n.
  Proof.
    iIntros "[% H]".
    iMod (own_update with "H") as "H".
    { apply auth_update_alloc.
      apply mnat_local_update; eauto. }
    by rewrite own_op; iDestruct "H" as "[$ $]".
  Qed.

  Lemma incr_Max γ n : Max γ n ==∗ Max γ (1 + n).
  Proof.
    iIntros "[% H]".
    iMod (own_update with "H") as "[$ _]"; last auto with lia.
    apply auth_update_alloc.
    apply mnat_local_update; eauto.
    apply Z2Nat.inj_le; auto with lia.
  Qed.

End ghost_theory.
