From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare weakestpre.
From iris.heap_lang Require Import notation proofmode lifting.
From DRADS Require Import increasing_ghost.

Definition incr : val :=
  rec: "loop" "l" :=
    let: "c" := !"l" in
    if: CAS "l" "c" (#1 + "c") then
      #()
    else
      "loop" "l".

Definition increasing : expr :=
  let: "l" := ref #0 in
  Fork ((rec: "do_incr" <> := incr "l";; "do_incr" #()) #());;
  let: "c" := ref #0 in
  (rec: "check_positive" <> :=
     let: "r" := ! "l" in
     if: !"c" ≤ "r" then "c" <- "r";; "check_positive" #() else #() #()
  ) #().

Section increasing.
  Context `{!heapG Σ, IncreasingG Σ}.

  Lemma increasing_spec :
  {{ True }} increasing {{ _, True }}.
  Proof.
    iAlways.
    iIntros "_".
    unfold increasing.
    wp_alloc l as "Hl".
    wp_let.
    iMod (IGT_alloc 0) as (γ) "Hmax"; first done.
    iMod (Observe with "Hmax") as "[Hmax Hseen]".
    iMod (inv_alloc
            (nroot.@"AP") _
            (∃ n : Z, Max γ n ∗ l ↦ #n) with "[Hl Hmax]")%I
      as "#Hinv".
    { iNext.
      iExists _.
      iFrame. }
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
      iDestruct "Hi" as (n) "[Hn Hl]".
      wp_load.
      iMod ("Hcl" with "[Hn Hl]") as "_".
      { iNext. by iExists _; iFrame. }
      iModIntro.
      wp_pures.
      wp_bind (CAS _ _ _)%E.
      iInv (nroot.@"AP") as ">Hi" "Hcl".
      iDestruct "Hi" as (n') "[Hn' Hl]".
      destruct (decide (n = n')).
      + subst.
        wp_cas_suc.
        iMod (incr_Max with "Hn'") as "Hn'".
        iMod ("Hcl" with "[Hn' Hl]") as "_".
        { iNext. by iExists _; iFrame. }
        iModIntro.
        wp_if.
        wp_seq.
        iApply "IH_do_incr".
      + wp_cas_fail.
        iMod ("Hcl" with "[Hn' Hl]") as "_".
        { iNext. by iExists _; iFrame. }
        iModIntro.
        wp_if.
        iApply "IH_incr".
    - wp_seq.
      wp_alloc c as "Hc".
      do 3 wp_pure _.
      generalize 0; intros z.
      iLöb as "IH_increasing" forall (z).
      wp_rec.
      wp_bind (! _)%E.
      iInv (nroot.@"AP") as ">Hi" "Hcl".
      iDestruct "Hi" as (n) "[Hn Hl]".
      iDestruct (Seen_le_Max with "Hn Hseen") as %?.
      iMod (Observe with "Hn") as "[Hn Hseen']".
      wp_load.
      iMod ("Hcl" with "[Hn Hl]") as "_".
      { iNext. by iExists _; iFrame. }
      iModIntro.
      wp_pures.
      wp_load.
      wp_op.
      rewrite bool_decide_true; trivial.
      wp_if.
      wp_store.
      iApply ("IH_increasing" with "Hseen' Hc").
  Qed.

End increasing.
