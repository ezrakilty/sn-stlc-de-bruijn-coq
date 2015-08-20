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

sn3.html: sn3.vo
	coqdoc -g sn3.v
