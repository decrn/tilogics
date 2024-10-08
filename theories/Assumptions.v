(******************************************************************************)
(* Copyright (c) 2024 Denis Carnier, Steven Keuchel                           *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Em Require Composition Gen.Bidirectional Gen.Check Gen.Synthesise
     Related.Gen.Bidirectional Related.Gen.Check Related.Gen.Synthesise
     Related.Monad.Free.

Goal True. idtac "Assumptions of check generator correctness:". Abort.
Print Assumptions Gen.Check.ocorrectness.

Goal True. idtac "Assumptions of synth generator correctness:". Abort.
Print Assumptions Gen.Synthesise.ocorrectness.

Goal True. idtac "Assumptions of bidirectional generator correctness:". Abort.
Print Assumptions Gen.Bidirectional.ocorrectness.

Goal True. idtac "Assumptions of end-to-end correctness:". Abort.
Print Assumptions Composition.correctness.

Goal True. idtac "Assumptions of decidability of typing :". Abort.
Print Assumptions Composition.decidability.

Goal True. idtac "Assumptions of check generator logical relatedness:". Abort.
Print Assumptions Related.Gen.Check.generate_correct_logrel.

Goal True. idtac "Assumptions of synth generator logical relatedness:". Abort.
Print Assumptions Related.Gen.Synthesise.generate_correct_logrel.

Goal True. idtac "Assumptions of bidirectional generator logical relatedness:". Abort.
Print Assumptions Related.Gen.Bidirectional.synth_correct_logrel.

Goal True. idtac "Assumptions of monad operation logical relatedness:". Abort.
Print Assumptions Related.Monad.Free.rtclogicmfree.
