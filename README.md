# Interactive Theorem Proving Framework for Declarative Cloud Orchestration

An interactive theorem proving framework for verifying liveness properties of declarative cloud orchestration is proposed.  The framework provides (1) a general way to formalize specifications of different kinds of cloud orchestration tools and (2) a procedure for how to verifying a kind of liveness properties of formalized specifications.  It also provides (a) general templates and libraries of formal descriptions for specifying orchestration of cloud systems and (b) logical proofs of lemmas for general predicates of the libraries.

The framework has been applied to the verification of specifications of AWS CloudFormation, of OASIS TOSCA, and also of Robust Reconfiguration Algorithm by F. Boyer et al., and is demonstrated to be effective for reducing generic routine work and making a verification engineer concentrate on the work specific to each individual system.

This package includes following files:

- README.md: This file.

- JAISTDoctoralDissertation.pdf: My doctoral dissertation on this work.
- UserGuide.pdf: User Guide for the framework.

- lib/Template.cafe: Template modules of objects.
- lib/SET.cafe: Utility module defining general sets.
- lib/BAG.cafe: Utility module defining general bags.
- lib/PNAT.cafe: Utility module defining Peano Style natural numbers.
- lib/NatAxiom.cafe: Utility module defining general axioms for natural numbers.
- lib/Lemmas.cafe: Proof scores for general lemmas.

- AWS/Domain.cafe: Specification of an AWS CloudFormation Template.
- AWS/Simulate.cafe: Example execution of the AWS CloudFormation Template.
- AWS/Proof.cafe: Common definitions for verification.
- AWS/Proof-initcont.cafe: Proof scores for condition (1).
- AWS/Proof-contcont.cafe: Common definitions for condition (2).
- AWS/Proof-contcont-R01.cafe: Proof scores for condition (2) for Rule R01.
- AWS/Proof-contcont-R02.cafe: Proof scores for condition (2) for Rule R02.
- AWS/Proof-measure.cafe: Proof scores for condition (3).
- AWS/Proof-inv.cafe: Proof scores for condition (4) and (5).
- AWS/all.cafe: Execute all proof scores.

- TOSCA/Domain.cafe: Specification of an OASIS TOSCA Topology.
- TOSCA/Simulate.cafe: Example execution of the OASIS TOSCA Topology.
- TOSCA/Proof.cafe: Common definitions for verification.
- TOSCA/Proof-initcont.cafe: Proof scores for condition (1).
- TOSCA/Proof-contcont.cafe: Common definitions for condition (2).
- TOSCA/Proof-contcont-R01.cafe: Proof scores for condition (2) for Rule R01.
- TOSCA/Proof-contcont-R02.cafe: Proof scores for condition (2) for Rule R02.
- TOSCA/Proof-contcont-R03.cafe: Proof scores for condition (2) for Rule R03.
- TOSCA/Proof-contcont-R04.cafe: Proof scores for condition (2) for Rule R04.
- TOSCA/Proof-contcont-R05.cafe: Proof scores for condition (2) for Rule R05.
- TOSCA/Proof-contcont-R06.cafe: Proof scores for condition (2) for Rule R06.
- TOSCA/Proof-contcont-R07.cafe: Proof scores for condition (2) for Rule R07.
- TOSCA/Proof-contcont-R08.cafe: Proof scores for condition (2) for Rule R08.
- TOSCA/Proof-contcont-R09.cafe: Proof scores for condition (2) for Rule R09.
- TOSCA/Proof-contcont-R10.cafe: Proof scores for condition (2) for Rule R10.
- TOSCA/Proof-contcont-R11.cafe: Proof scores for condition (2) for Rule R11.
- TOSCA/Proof-contcont-R12.cafe: Proof scores for condition (2) for Rule R12.
- TOSCA/Proof-measure.cafe: Proof scores for condition (3).
- TOSCA/Proof-inv.cafe: Proof scores for condition (4) and (5).
- TOSCA/Proof-lemma.cafe: Proof scores for lemmas specific to this problem.
- TOSCA/Proof-cyclelemma.cafe: Proof scores for two special lemmas.
- TOSCA/all.cafe: Execute all proof scores.

- CafeOBJ/*.cafe: Sample proof scores for the preliminaries of CafeOBJ.

CafeOBJ system can be downloaded at http://cafeobj.org.