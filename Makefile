COQC = coqc

%.vo: %.v
	$(COQC) $< -R Listkit Listkit

all: sn.vo index.html

Term.vo: Listkit/listkit.vo

Monomorphism.vo: Listkit/listkit.vo

Shift.vo: eztactics.v Term.vo Monomorphism.vo

Subst.vo: eztactics.v Term.vo Typing.vo Shift.vo OutsideRange.vo

Rewrites.vo: Shift.vo Subst.vo

Norm.vo: eztactics.v Shift.vo Subst.vo Rewrites.vo

Typing.vo: Term.vo

OutsideRange.vo: eztactics.v

Continuation.vo: Term.vo Norm.vo

Knorm.vo: Continuation.vo Rewrites.vo Norm.vo Term.vo

sn.vo: eztactics.v Listkit/listkit.vo Term.vo Shift.vo Subst.vo Rewrites.vo \
	Norm.vo Typing.vo Monomorphism.vo OutsideRange.vo Continuation.vo Knorm.vo

%.html: %.v %.vo
	coqdoc -g -d docs $<

# index.html: sn.html eztactics.v Listkit/listkit.html Term.html		\
# 	Shift.html Subst.html Rewrites.html Norm.html Typing.html	\
# 	Monomorphism.html OutsideRange.html

LISTKIT_FILES = Listkit/logickit.v Listkit/NthError.v			\
                Listkit/Concat.v Listkit/Foreach.v Listkit/Max.v	\
                Listkit/TakeDrop.v Listkit/RangeSet.v Listkit/All.v	\
                Listkit/AllType.v Listkit/Map.v Listkit/Sets.v

Listkit/listkit.vo:
	make -f Listkit/Makefile $@

FILES = sn.v Term.v Shift.v Subst.v Rewrites.v Knorm.v \
	Norm.v Typing.v Monomorphism.v OutsideRange.v Continuation.v \
	$(LISTKIT_FILES)

index.html: $(FILES) coqdoc.css
	mkdir -p docs
	coqdoc -g --utf8 -d docs/ $(FILES)
	# Overwrite the bad CSS coqdoc gives us.
	cp coqdoc.css docs/
