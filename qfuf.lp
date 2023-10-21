constant symbol Prop : TYPE;
injective symbol Prf : Prop → TYPE;
constant symbol ⊤ : Prop;
rule Prf ⊤ ↪ Π r, Prf r → Prf r;
constant symbol ⊥ : Prop;
rule Prf ⊥ ↪ Π r, Prf r;

symbol Set : TYPE;
symbol Term : Set → TYPE;
constant symbol Bool: Set;
rule Term Bool ↪ Prop;


// equality for Bool
symbol = : Term Bool → Term Bool → Prop;
notation = infix 1;

// equality for types other than Bool. polymorphic
symbol ≃ [a : Set] : Term a → Term a → Prop;
notation ≃ infix 1;

constant symbol ¬ : Prop → Prop; notation ¬ prefix 40;
rule Prf (¬ $p) ↪ Prf $p → Π r, Prf r;
constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 30;
rule Prf ($p ∧ $q) ↪ Π r, (Prf $p → Prf $q → Prf r) → Prf r;
constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix right 20;
rule Prf ($p ∨ $q) ↪ Π r, (Prf $p → Prf r) → (Prf $q → Prf r) → Prf r;
constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 10;
rule Prf ($x ⇒ $y) ↪ Prf $x → Prf $y;
constant symbol xor : Prop → Prop → Prop; notation xor infix right 35;
rule Prf ($x xor $y) ↪ Prf (($x ∨ $y) ∧ ¬ ($x ∧ $y));

symbol prop_ext1 p q : Prf ((p ⇒ q) ∧ (q ⇒ p)) → Prf (p = q);
symbol prop_ext2 p q : Prf (p = q) → Prf ((p ⇒ q) ∧ (q ⇒ p));
symbol classic p : Prf (¬ ¬ p) → Prf p;

symbol ∧e2 phi1 phi2 : Prf (phi1 ∧ phi2) → Prf (phi2) ≔ begin 
    assume phi1 phi2 h1;
    apply h1; assume pphi1 pphi2;
    refine pphi2;
end;

symbol ∧e1 phi1 phi2 : Prf (phi1 ∧ phi2) → Prf (phi1) ≔ begin 
    assume phi1 phi2 x;
    apply x; assume pphi1 pphi2;
    refine pphi1;
end;

symbol ∧i p q : Prf p → Prf q → Prf (p ∧ q) ≔ begin 
    assume p q pp pq;
    assume r h1;
    apply h1 pp;
    apply pq;
end;


symbol ∨i1 p q : Prf p → Prf (p ∨ q) ≔ begin
    assume p q pp;
    assume r pr qr;
    apply pr pp;
    // refine (λ r pr qr, pr pp);
end;

symbol ∨i2 p q : Prf q → Prf (p ∨ q) ≔ begin
    assume p q pq;
    refine (λ r pr qr, qr pq);
end;

symbol ∨e p q r : Prf (p ∨ q) → (Prf p → Prf r) → (Prf q → Prf r) → Prf r ≔ begin 
    assume p q r poq pr qr;
    apply poq {refine pr} {refine qr};
end;

symbol ⊥e r : Prf ⊥ → Prf r ≔ begin 
    assume r pb;
    apply pb;
end;


symbol true : Prf (⊤);
symbol false : Prf (¬ ⊥);
symbol eq_reflexive x : Prf (x = x);

symbol not_not p : Prf (p ∨ ¬ ¬ ¬ p) ≔ begin 
    assume p;
    apply classic;
    assume contradiction;
    refine contradiction _;
    assume r1 ;
    assume left1 right1;
    apply left1;
    apply classic;
    assume np;
    refine contradiction _;
    assume r2;
    assume left2 right2;
    apply right2;
    assume nnp;
    refine nnp np;
end;

symbol not_implies1 p q : Prf ¬ (p ⇒ q) → Prf p ≔ begin 
    assume p q nh;
    apply classic;
    assume np;
    refine nh _;
    assume pp;
    apply ⊥e;
    refine np pp;
end;

symbol not_implies2 p q : Prf (¬ (p ⇒ q)) → Prf (¬ q) ≔ begin 
    assume p q nh;
    apply classic;
    assume nnq;
    refine nh _;
    assume pp;
    apply classic _ nnq;
end;

symbol implies_neg1 p q : Prf ((p ⇒ q) ∨ p) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume r1;
    assume left1 right1;
    apply left1;
    apply classic;
    assume npq;
    refine nh _;
    assume r2;
    assume left2 right2;
    refine right2 _;
    apply npq;
    assume pp;
    apply classic;
    assume nq;
    refine nh _;
    assume r3 left3 right3;
    apply right3 pp;
end;

symbol implies_neg2 p q : Prf ((p ⇒ q) ∨ ¬ q) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume r1 left1 right1;
    apply left1;
    apply classic;
    assume npq;
    refine nh _;
    assume r2 left2 right2 ;
    apply right2;
    assume prfq;
    refine nh _;
    assume r3 left3 right3;
    apply left3;
    assume pp;
    refine prfq;
end;

symbol xor1 p q : Prf (p xor q) → Prf (p ∨ q) ≔ begin
    assume p q pxq;
    apply classic;
    assume npoqc;
    refine npoqc _;
    assume s1;
    assume left1 right1;
    apply left1;
    apply classic;
    assume np;
    refine npoqc _;
    refine pxq _ _;
    assume h3 h4;
    refine h3;
end;

symbol xor2 p q : Prf (p xor q) → Prf (¬ p ∨ ¬ q) ≔ begin 
    assume p q pxcq;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume pp;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    assume pq;
    have npaq : Prf (¬ (p ∧ q)) {
        refine pxcq _ _; 
        assume h2 h3; 
        refine h3;
    };
    have paq : Prf (p ∧ q) {
        refine ∧i _ _ pp pq;
    };
    refine npaq paq;
end;

symbol not_xor1 p q : Prf (¬ (p xor q)) → Prf (p ∨ ¬ q) ≔ begin
    assume p q ass;
    apply classic;
    assume nh;
    refine ass _;
    apply classic;
    assume h2;
    refine nh _;
    assume s1 left1 right1;
    apply right1;
    assume pq;
    refine nh _;
    assume s2 left2 right2;
    apply left2;
    apply classic;
    assume np;
    refine h2 _;
    have npaq : Prf (¬ (p ∧ q)) {
        assume paq;
        have pp : Prf p { 
            refine ∧e1 _ _ paq;
        };
        refine np pp;
    };
    have poq : Prf (p ∨ q) {refine ∨i2 _ _ pq;};
    refine ∧i (p ∨ q) (¬ (p ∧ q)) poq npaq;
end;

symbol not_xor2 p q : Prf (¬ (p xor q)) → Prf (¬ p ∨ q) ≔ begin 
    assume p q ass;
    apply classic;
    assume nh;
    refine ass _;
    apply classic;
    assume h2;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume pp;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    apply classic;
    assume nq;
    refine h2 _;
    have npaq : Prf (¬ (p ∧ q)) {
        assume paq;
        have pq : Prf q { 
            refine ∧e2 _ _ paq;
        };
        refine nq pq;
    };
    have poq : Prf (p ∨ q) {
        refine ∨i1 _ _ pp;
    };
    refine ∧i (p ∨ q) (¬ (p ∧ q)) poq npaq;
end;

symbol intuition p : Prf p → Prf ¬ ¬ p ≔ begin 
    assume p pp np;
    refine np pp;
end;


symbol implies p q : Prf (p ⇒ q) → Prf (¬ p ∨ q) ≔ begin 
    assume p q ass;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume pp;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    refine ass pp;
end;

symbol equiv_simplify1 p q : Prf (p = q) → Prf (p ⇒ q) ≔ begin 
    assume p q ass;
    have peq : Prf ((p ⇒ q) ∧ (q ⇒ p)) {refine prop_ext2 _ _ ass;};
    refine ∧e1 _ _ peq;
end;

symbol equiv_simplify2 p q : Prf (p = q) → Prf (q ⇒ p) ≔ begin 
    assume p q ass;
    have peq : Prf ((p ⇒ q) ∧ (q ⇒ p)) {refine prop_ext2 _ _ ass;};
    refine ∧e2 _ _ peq;
end;

symbol equiv1 p q : Prf (p = q) → Prf (¬ p ∨ q) ≔ begin 
    assume p q ass;
    have piq : Prf (p ⇒ q) {refine equiv_simplify1 _ _ ass;};
    // have piqc : Prfc (p ⇒c q) {refine intuition _ piq;};
    refine implies _ _ piq;
end;

symbol ∨refl p q : Prf (p ∨ q) → Prf (q ∨ p) ≔ begin 
    assume p q ass;
    assume s1 left1 right1;
    refine ass s1 right1 left1;
end;

symbol equiv2 p q : Prf (p = q) → Prf (p ∨ ¬ q) ≔ begin 
    assume p q ass;
    have qip : Prf (q ⇒ p) {
        refine equiv_simplify2 _ _ ass;
    };
    have nqop : Prf (¬ q ∨ p) {
        refine implies _ _ qip;
    };
    refine ∨refl _ _ nqop;
end;

symbol not_equiv1 p q : Prf ¬ (p = q) → Prf (p ∨ q) ≔ begin 
    assume p q ass;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    apply classic;
    assume np;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    apply classic;
    assume nq;
    refine ass _;
    have peq : Prf ((p ⇒ q) ∧ (q ⇒ p)) {
        assume s3;
        assume left3;
        refine left3 _ _ 
        {
            assume pp;
            apply classic;
            assume nq1;
            refine np pp;
        } 
        {
            assume pq;
            apply classic;
            assume np1;
            refine nq pq;
        };
    };
    refine prop_ext1 p q peq;
end;


symbol not_equiv2 p q : Prf ¬ (p = q) → Prf (¬ p ∨ ¬ q) ≔ begin 
    assume p q ass;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume pp;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    assume pq;
    refine ass _;
    have peq : Prf ((p ⇒ q) ∧ (q ⇒ p)) {
        assume s3;
        assume left3;
        refine left3 _ _ 
        {
            assume pp1;
            refine pq;
        } 
        {
            assume pq1;
            refine pp;
        };
    };
    refine prop_ext1 p q peq;
end;

symbol equiv_pos1 p q : Prf (¬ (p = q) ∨ p ∨ ¬ q) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume peq;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    refine equiv2 p q _;
    refine peq;
end;

symbol equiv_pos2 p q : Prf (¬ (p = q) ∨ ¬ p ∨ q) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    assume peq;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    refine equiv1 p q _;
    refine peq;
end;

symbol equiv_neg1 p q : Prf ((p = q) ∨ p ∨ q) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    apply classic;
    assume npeq;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    refine not_equiv1 p q _;
    refine npeq;
end;

symbol equiv_neg2 p q : Prf ((p = q) ∨ ¬ p ∨ ¬ q) ≔ begin 
    assume p q;
    apply classic;
    assume nh;
    refine nh _;
    assume s1 left1 right1;
    apply left1;
    apply classic;
    assume npeq;
    refine nh _;
    assume s2 left2 right2;
    apply right2;
    refine not_equiv2 p q _;
    refine npeq;
end;
