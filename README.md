Mechanization (in the Coq proof assistant) of a synthetic many-one reduction from the binary modified Post correspondence problem `PCP.BMPCP` to the following two problems for propositional calculi:

- recognizing axiomatizations of Hilbert-style calculi (`HSC.HSC_AX`)
- provability in Hilbert-style calculi (`HSC.HSC_PRV`)

The reduction from `BMPCP` to `HSC_AX` is mechanized as `Theorem BMPCP_to_HSC_AX : BMPCP ⪯ HSC_AX.` in `HSC/HSC_AX/BMPCP_to_HSC_AX.v`.

The reduction from `BMPCP` to `HSC_PRV` is mechanized as `Theorem BMPCP_to_HSC_PRV : BMPCP ⪯ (HSC_PRV ΓPCP).` in `HSC/HSC_PRV/BMPCP_to_HSC_PRV.v`.

Build instructions: 
```
install Coq (8.11) 
cd 2020-types-propositional-calculi
make
```
