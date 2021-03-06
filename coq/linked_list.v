From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare weakestpre.
From iris.heap_lang Require Import notation proofmode lifting.

(*

Linked list:

Head |-> option (data * Next)

Next |-> option (data * Next)

 *)


Definition ll_reverse_acc : val :=
  (rec: "rev" "l" "acc" :=
     match: !"l" with
       NONE => "acc"
     | SOME "x" =>
       let: "newacc" := ref (SOME (Fst "x", "acc")) in
       let: "next" := (Snd "x") in
       "rev" "next" "newacc"
     end
  )%V.

Definition ll_reverse : val :=
  λ: "l", let: "emp" := (ref NONE) in ll_reverse_acc "l" "emp".

Section ll_reverse.
  Context `{!heapG Σ}.

  Fixpoint is_ll (head : loc) (lst : list val) : iProp Σ :=
    match lst with
    | [] => head ↦ NONEV
    | (h :: t) => ∃ (lnext : loc), head ↦ SOMEV (h, #lnext) ∗ is_ll lnext t
    end%I.

  Lemma ll_reverse_acc_spec head lst acc acclst:
  {{is_ll head lst ∗ is_ll acc acclst }} (ll_reverse_acc #head) #acc
  {{ v, ∃ l : loc, ⌜v = #l⌝ ∗ is_ll l (rev lst ++ acclst) }}.
  Proof.
    iAlways.
    iIntros "[Hhead Hacc]".
    iInduction lst as [] "IH" forall (head acc acclst).
    - unfold ll_reverse_acc; simpl.
      wp_rec.
      wp_let.
      wp_load.
      wp_match.
      iExists acc.
      iFrame.
      trivial.
    - simpl.
      iDestruct "Hhead" as (lnext) "[Hhead Htail]".
      unfold ll_reverse_acc at 2; simpl.
      wp_rec.
      fold ll_reverse_acc.
      wp_let.
      wp_load.
      wp_match.
      wp_proj.
      wp_alloc nacc as "Hnacc".
      wp_let.
      wp_proj.
      wp_let.
      rewrite -app_assoc; simpl.
      iApply ("IH" with "Htail").
      simpl.
      iExists acc.
      iFrame.
  Qed.

  Theorem ll_reverse_spec head lst :
    {{ is_ll head lst }}
       ll_reverse #head
    {{v, ∃ l : loc, ⌜v = #l⌝ ∗ is_ll l (rev lst) }}.
  Proof.
    iAlways.
    iIntros "Hpre".
    unfold ll_reverse.
    wp_lam.
    wp_alloc em as "Hem".
    wp_let.
    rewrite -[rev lst]app_nil_r.
    iApply (ll_reverse_acc_spec with "[Hpre Hem]").
    iFrame.
  Qed.

End ll_reverse.
