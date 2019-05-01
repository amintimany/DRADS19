From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare weakestpre.
From iris.heap_lang Require Import notation proofmode lifting.


Definition incr : val :=
  rec: "loop" "l" :=
    let: "c" := !"l" in
    if: CAS "l" "c" (#1 + "c") then
      #()
    else
      "loop" "l".

Definition always_positive : expr :=
  let: "l" := ref #0 in
  Fork ((rec: "do_incr" <> := incr "l";; "do_incr" #()) #());;
  (rec: "check_positive" <> :=
     if: #0 ≤ !"l" then "check_positive" #() else #() #()
  ) #().

Section always_positive.
  Context `{!heapG Σ}.

  Lemma always_positive_spec :
  {{ True }} always_positive {{ _, True }}.
  Proof.
    iAlways.
    iIntros "_".
    unfold always_positive.
    wp_alloc l as "Hl".
    wp_let.
    iMod (inv_alloc (nroot.@"AP") _ (∃ n : Z, ⌜0 ≤ n⌝ ∗ l ↦ #n) with "[Hl]")%I
      as "#Hinv".
    { iNext.
      iExists 0.
      iFrame.
      trivial. }
    About wp_fork.
    wp_apply wp_fork.
    - wp_pure _.
      iLöb as "IH_do_incr".
      wp_pures.
      wp_bind (incr _).
      unfold incr at 2.
      iLöb as "IH_incr".
      wp_rec.
      wp_bind (! _)%E.
      iInv (nroot.@"AP") as ">Hi" "Hcl".
      iDestruct "Hi" as (n Hn) "Hl".
      wp_load.
      iMod ("Hcl" with "[Hl]") as "_".
      { iNext. by iExists _; iFrame. }
      iModIntro.
      wp_pures.
      wp_bind (CAS _ _ _)%E.
      iInv (nroot.@"AP") as ">Hi" "Hcl".
      iDestruct "Hi" as (n' Hn') "Hl".
      destruct (decide (n = n')).
      + subst.
        wp_cas_suc.
        iMod ("Hcl" with "[Hl]") as "_".
        { iNext. iExists _; iFrame. auto with lia. }
        iModIntro.
        wp_if.
        wp_seq.
        iApply "IH_do_incr".
      + wp_cas_fail.
        iMod ("Hcl" with "[Hl]") as "_".
        { iNext. by iExists _; iFrame. }
        iModIntro.
        wp_if.
        iApply "IH_incr".
    - wp_seq.
      wp_pure _.
      iLöb as "IH_check_positive".
      wp_rec.
      wp_bind (! _)%E.
      iInv (nroot.@"AP") as ">Hi" "Hcl".
      iDestruct "Hi" as (n Hn) "Hl".
      wp_load.
      iMod ("Hcl" with "[Hl]") as "_".
      { iNext. by iExists _; iFrame. }
      iModIntro.
      wp_op.
      rewrite bool_decide_true; trivial.
      wp_if.
      iApply "IH_check_positive".
  Qed.

End always_positive.
