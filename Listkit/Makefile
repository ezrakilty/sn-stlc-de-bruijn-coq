COQC = coqc

%.vo: %.v
	$(COQC) $< -R Listkit Listkit

Listkit/%.vo: %.v
	$(COQC) $< -R Listkit Listkit

Listkit/NthError.vo: eztactics.v Listkit/logickit.vo

Listkit/Sets.vo: Listkit/Foreach.vo Listkit/logickit.vo Listkit/NthError.vo

Listkit/All.vo: eztactics.v Listkit/Sets.vo Listkit/logickit.vo

Listkit/AllType.vo: Listkit/Sets.vo

Listkit/Subseteq.vo: eztactics.v Listkit/Sets.vo

Listkit/Map.vo: Listkit/Sets.vo

Listkit/listkit.vo: Listkit/logickit.vo Listkit/NthError.vo \
                    Listkit/Concat.vo Listkit/Foreach.vo Listkit/Max.vo \
                    Listkit/TakeDrop.vo Listkit/RangeSet.vo \
                    Listkit/All.vo Listkit/AllType.vo Listkit/Map.vo \
                    Listkit/Sets.vo Listkit/Subseteq.vo
