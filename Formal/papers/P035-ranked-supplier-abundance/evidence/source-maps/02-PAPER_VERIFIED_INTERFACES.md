# Authenticated theorem interfaces

## RAF.Frankl.locally_ranked_supplier_abundance

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] [inst_1 : Fintype.{u_2} R]
[inst_2 : DecidableEq.{u_2 + 1} R] (Q : @RAF.CRS.{u_1, u_2} M R inst) (C : RAF.Catalysis.{u_1, u_2} M R)
(U : Finset.{u_2} R) (rank : R → Nat) (hrank : @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q U rank)
(hU : @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C U),
And (@RAF.IsRAF.{u_1, u_2} M R inst Q C U)
(And
(∀ (T : Finset.{u_2} R),
@LE.le.{0} Nat instLENat
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@Finset.card.{u_2}
(Finset.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r))
(@RAF.Frankl.extensionFibre.{u_1, u_2} M R inst inst_1 inst_2 Q C U T))
(@Fintype.card.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@Finset.Subtype.fintype.{u_2} R U)))
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
(@Finset.sum.{u_2, 0}
(Finset.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r))
Nat Nat.instAddCommMonoid (@RAF.Frankl.extensionFibre.{u_1, u_2} M R inst inst_1 inst_2 Q C U T)
fun
(S :
Finset.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)) =>
@Finset.card.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
S)))
(And
(@LE.le.{0} Nat instLENat
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@Finset.card.{u_2} (Finset.{u_2} R) (@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))
(@Finset.card.{u_2} R U))
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Nat Nat.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) =>
@Finset.card.{u_2} R (@Inter.inter.{u_2} (Finset.{u_2} R) (@Finset.instInter.{u_2} R inst_2) W U))))
(@Exists.{u_2 + 1} R fun (r : R) =>
And
(@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@LE.le.{0} Nat instLENat
(@Finset.card.{u_2} (Finset.{u_2} R) (@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
(@Finset.card.{u_2} (Finset.{u_2} R)
(@Finset.filter.{u_2} (Finset.{u_2} R)
(fun (W : Finset.{u_2} R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) W r)
(fun (a : Finset.{u_2} R) => @Finset.decidableMem.{u_2} R inst_2 r a)
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))))))))
```

## RAF.Frankl.local_supplier_bounded_weights

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] [inst_1 : Fintype.{u_2} R]
[inst_2 : DecidableEq.{u_2 + 1} R] (Q : @RAF.CRS.{u_1, u_2} M R inst) (C : RAF.Catalysis.{u_1, u_2} M R)
(U : Finset.{u_2} R) (rank : R → Nat) (hrank : @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q U rank)
(hU : @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C U) (w lo : Finset.{u_2} R → Real) (k : Real)
(hlo :
∀ (T : Finset.{u_2} R),
@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (lo T))
(hk : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) k)
(hw :
∀ (W : Finset.{u_2} R),
@Membership.mem.{u_2, u_2} (Finset.{u_2} R) (Finset.{u_2} (Finset.{u_2} R))
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} (Finset.{u_2} R)) (Finset.{u_2} R)
(@Finset.instSetLike.{u_2} (Finset.{u_2} R)))
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) W →
And
(@LE.le.{0} Real Real.instLE (lo (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U))
(w W))
(@LE.le.{0} Real Real.instLE (w W)
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
(lo (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U))))),
And
(@LE.le.{0} Real Real.instLE
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_2} R U))
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) => w W))
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
(@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) k)
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) =>
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (w W)
(@Nat.cast.{0} Real Real.instNatCast
(@Finset.card.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@RAF.Frankl.toRestricted.{u_2} R U W))))))
(@Exists.{u_2 + 1} R fun (r : R) =>
And
(@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@LE.le.{0} Real Real.instLE
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) => w W)
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
(@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) k)
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@Finset.filter.{u_2} (Finset.{u_2} R)
(fun (W : Finset.{u_2} R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) W r)
(fun (a : Finset.{u_2} R) => @Finset.decidableMem.{u_2} R inst_2 r a)
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))
fun (W : Finset.{u_2} R) => w W))))
```

## RAF.Frankl.local_supplier_exterior_weights

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] [inst_1 : Fintype.{u_2} R]
[inst_2 : DecidableEq.{u_2 + 1} R] (Q : @RAF.CRS.{u_1, u_2} M R inst) (C : RAF.Catalysis.{u_1, u_2} M R)
(U : Finset.{u_2} R) (rank : R → Nat) (hrank : @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q U rank)
(hU : @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C U) (h : Finset.{u_2} R → Real)
(hh :
∀ (T : Finset.{u_2} R),
@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (h T)),
And
(@LE.le.{0} Real Real.instLE
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{u_2} R U))
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) =>
h (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U)))
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@OfNat.ofNat.{0} Real (nat_lit 2)
(@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
(@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) =>
@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(h (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U))
(@Nat.cast.{0} Real Real.instNatCast
(@Finset.card.{u_2}
(@Subtype.{u_2 + 1} R fun (r : R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@RAF.Frankl.toRestricted.{u_2} R U W))))))
(@Exists.{u_2 + 1} R fun (r : R) =>
And
(@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@LE.le.{0} Real Real.instLE
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1) fun (W : Finset.{u_2} R) =>
h (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U))
(@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
(@OfNat.ofNat.{0} Real (nat_lit 2)
(@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
(@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
(@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
(@Finset.sum.{u_2, 0} (Finset.{u_2} R) Real Real.instAddCommMonoid
(@Finset.filter.{u_2} (Finset.{u_2} R)
(fun (W : Finset.{u_2} R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) W r)
(fun (a : Finset.{u_2} R) => @Finset.decidableMem.{u_2} R inst_2 r a)
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))
fun (W : Finset.{u_2} R) =>
h (@SDiff.sdiff.{u_2} (Finset.{u_2} R) (@Finset.instSDiff.{u_2} R inst_2) W U)))))
```

## RAF.Frankl.LocalSupplierExample.exact_fixed_family

```lean
@Eq.{1}
(Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@RAF.Frankl.fixedFamily.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
RAF.Frankl.LocalSupplierExample.source RAF.Frankl.LocalSupplierExample.catalysts
(SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
(@Insert.insert.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@Finset.instInsert.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
fun (a b : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) =>
@Finset.decidableEq.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) a b)
(@EmptyCollection.emptyCollection.{0}
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instEmptyCollection.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@Insert.insert.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@Finset.instInsert.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
fun (a b : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) =>
@Finset.decidableEq.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) a b)
(@Insert.insert.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instInsert.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
(SimplexCategory.instOfNatToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)))
(@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
(SimplexCategory.instOfNatToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)))))
(@Singleton.singleton.{0, 0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(Finset.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@Finset.instSingleton.{0} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
(@Insert.insert.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instInsert.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
(SimplexCategory.instOfNatToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)))
(@Insert.insert.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instInsert.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
(SimplexCategory.instOfNatToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)))
(@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
(Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
(@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
(SimplexCategory.instOfNatToTypeOrderHomFinHAddNatLenOfNat
(SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 2)))))))))
```

## RAF.Frankl.local_supplier_deletion

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] [inst_1 : Fintype.{u_2} R]
[inst_2 : DecidableEq.{u_2 + 1} R] (Q : @RAF.CRS.{u_1, u_2} M R inst) (C : RAF.Catalysis.{u_1, u_2} M R)
(U : Finset.{u_2} R) (rank : R → Nat) (hrank : @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q U rank)
(hU : @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C U),
@Exists.{u_2 + 1} R fun (r : R) =>
And
(@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r)
(@LE.le.{0} Nat instLENat
(@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
(@Finset.card.{u_2} (Finset.{u_2} R) (@RAF.Frankl.survivingRAFs.{u_1, u_2} M R inst inst_1 inst_2 Q C r)))
(@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
(@Finset.card.{u_2} (Finset.{u_2} R) (@RAF.Frankl.rafFamily.{u_1, u_2} M R inst Q C inst_1)))
```

## RAF.Frankl.disjoint_local_cores_witnesses

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] [inst_1 : Fintype.{u_2} R]
[inst_2 : DecidableEq.{u_2 + 1} R] {I : Type u_3} (Q : @RAF.CRS.{u_1, u_2} M R inst)
(C : RAF.Catalysis.{u_1, u_2} M R) (U : I → Finset.{u_2} R) (rank : I → R → Nat)
(hrank : ∀ (i : I), @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q (U i) (rank i))
(hU : ∀ (i : I), @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C (U i))
(hd :
∀ (i j : I),
@Ne.{u_3 + 1} I i j →
@Disjoint.{u_2} (Finset.{u_2} R) (@Finset.partialOrder.{u_2} R) (@Finset.instOrderBot.{u_2} R) (U i) (U j)),
@Exists.{max (u_2 + 1) (u_3 + 1)} (I → R) fun (f : I → R) =>
And (@Function.Injective.{u_3 + 1, u_2 + 1} I R f)
(∀ (i : I),
And
(@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) (U i) (f i))
(@LE.le.{0} Nat instLENat
(@Finset.card.{u_2} (Finset.{u_2} R) (@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))
(@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
(@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
(@Finset.card.{u_2} (Finset.{u_2} R)
(@Finset.filter.{u_2} (Finset.{u_2} R)
(fun (W : Finset.{u_2} R) =>
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) W (f i))
(fun (a : Finset.{u_2} R) => @Finset.decidableMem.{u_2} R inst_2 (f i) a)
(@RAF.Frankl.fixedFamily.{u_1, u_2} M R inst Q C inst_1))))))
```

## RAF.Frankl.local_certificate_transport

```lean
∀ {M : Type u_1} {R : Type u_2} [inst : DecidableEq.{u_1 + 1} M] (Q Q' : @RAF.CRS.{u_1, u_2} M R inst)
(C C' : RAF.Catalysis.{u_1, u_2} M R) (U : Finset.{u_2} R) (rank : R → Nat)
(hrank : @RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q U rank)
(hU : @RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q C U)
(hf :
@HasSubset.Subset.{u_1} (Finset.{u_1} M) (@Finset.instHasSubset.{u_1} M) (@RAF.CRS.food.{u_1, u_2} M R inst Q)
(@RAF.CRS.food.{u_1, u_2} M R inst Q'))
(hi :
∀ (r : R),
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r →
@Eq.{u_1 + 1} (Finset.{u_1} M) (@RAF.CRS.inputs.{u_1, u_2} M R inst Q' r)
(@RAF.CRS.inputs.{u_1, u_2} M R inst Q r))
(ho :
∀ (r : R),
@Membership.mem.{u_2, u_2} R (Finset.{u_2} R)
(@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} R) R (@Finset.instSetLike.{u_2} R)) U r →
@Eq.{u_1 + 1} (Finset.{u_1} M) (@RAF.CRS.outputs.{u_1, u_2} M R inst Q' r)
(@RAF.CRS.outputs.{u_1, u_2} M R inst Q r))
(hc : ∀ (x : M) (r : R), C x r → C' x r),
And (@RAF.Frankl.InternalSubstrateRank.{u_1, u_2} M R inst Q' U rank)
(@RAF.Frankl.SupplierCore.{u_1, u_2} M R inst Q' C' U)
```
