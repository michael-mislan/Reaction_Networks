# Metered finite food: exact coupling and preparation accounting

Fix a finite mission of m cycles, volume V, and an admitted feedback policy. Start from the same prepared internal state and the same finite fuel/waste state as in the compiled mission theorem. Let P_U,P_W be the food actually charged to the chosen preparation procedure. Preparation is an explicit input here: the theorem does not construct catalytic stock from a food-only start or assert that its elemental content is its entire preparation cost.

Allocate initial inventories

    B_U = P_U + 5mV + 1,   B_W = P_W + 5mV + 1.

After preparation, each food stock therefore contains 5mV+1 molecules. Both the continuous food arrivals and every intervention bolus debit these stocks. Harvested material does not replenish them. Food is metered by an ideal controller: while stock is available its arrival propensity remains V. This is not a finite passive bath whose arrival rate is proportional to its remaining inventory. On stockout the operation shuts down. The fuel/waste bath remains the separate finite mass-action bath already proved above.

## Common-randomness construction

Construct the maintained-food and metered-food processes together. Whenever their full states agree and both food stocks are positive, use the same exponential waiting draw and the same reaction-label draw. Their complete propensity vectors agree there, so the event time, chosen label, internal update and bath update agree exactly. Debit one food molecule on the relevant arrival label. Use the same pulse outcome for an intervention and debit its specified integer boluses; if a bolus cannot be supplied, shut down before executing it. Continue this common construction until the first shortage, if one occurs. Thereafter hold the metered process at its shutdown state. The maintained process continues with its original law.

This recursively defines a coupling through each finite collection of jumps and pulses. The compiled nonexplosion theorem ensures finitely many chemical jumps on every bounded mission interval almost surely; there are only finitely many prescribed pulses. Thus the construction is defined throughout the mission. Before shutdown the metered marginal has exactly the prescribed metered propensity vector and pulse law. The absorbing shutdown convention gives its behavior afterward. No success conditioning, renormalization or post hoc resampling is used.

On the maintained process's joint operational success event, total continuous-plus-bolus food use in each species is at most 5mV. The counters are nondecreasing at every chemical prefix; their initial per-cycle values already include the bolus. Hence every prefix of the entire mission has consumption at most 5mV. The spare molecule makes both stocks strictly positive throughout that event. Every bolus fits as well, because the prefix immediately after its debit is included. Consequently shortage never occurs on that event, and the coupled processes agree in all physical states, pulse outcomes, jump labels, event times and collected outputs throughout the mission.

It follows by inclusion of this event in the metered process's success event that the metered mission has at least the same success probability. All finite fuel/waste prefix and activity consequences hold on the same coupled event. Finite food supply thus bounds a prescribed finite mission; this statement makes no claim of indefinite operation with a finite food inventory.

## Evidence boundary

`MeteredFood.lean` proves exact propensity-vector agreement before stockout and the nondecreasing chemical/cycle/history counters, including the boluses and the strict inventory inequality with preparation charged. `Mission.lean` and `InverseDesign.lean` prove the maintained-food probability bound and finite-bath consequences in Lean. The common-randomness construction and its metered-law probability transfer in the preceding paragraphs are a conventional mathematical coupling proof, not a separately kernel-checked metered path-measure construction. This distinction must remain explicit in the final report.
