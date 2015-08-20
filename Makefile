COQC = coqc

%.vo: %.v
	$(COQC) $< -R Listkit Listkit

all: sn3.vo sn3.html

Term.vo: Listkit/listkit.vo

Monomorphism.vo: Listkit/listkit.vo

Shift.vo: eztactics.v Term.vo Monomorphism.vo

Subst.vo: eztactics.v Term.vo Typing.vo Shift.vo OutsideRange.vo

Rewrites.vo: Shift.vo Subst.vo

Norm.vo: eztactics.v Shift.vo Subst.vo Rewrites.vo

Typing.vo: Term.vo

OutsideRange.vo: eztactics.v

sn3.vo: eztactics.v Listkit/listkit.vo Term.vo Shift.vo Subst.vo Rewrites.vo \
	Norm.vo Typing.vo Monomorphism.vo OutsideRange.vo

%.html: %.v %.vo
	coqdoc -g -d docs $<

# index.html: sn3.html eztactics.v Listkit/listkit.html Term.html		\
# 	Shift.html Subst.html Rewrites.html Norm.html Typing.html	\
# 	Monomorphism.html OutsideRange.html

LISTKIT_FILES = Listkit/logickit.v Listkit/NthError.v			\
                Listkit/Concat.v Listkit/Foreach.v Listkit/Max.v	\
                Listkit/TakeDrop.v Listkit/RangeSet.v Listkit/All.v	\
                Listkit/AllType.v Listkit/Map.v Listkit/Sets.v		\
                Listkit/Subseteq.v


FILES = Term.v Shift.v Subst.v Rewrites.v \
	Norm.v Typing.v Monomorphism.v OutsideRange.v \
	$(LISTKIT_FILES)

index.html: Listkit/listkit.v Term.v Shift.v Subst.v Rewrites.v \
	Norm.v Typing.v Monomorphism.v OutsideRange.v
	mkdir -p docs
	coqdoc -g --utf8 -d docs $(FILES)
