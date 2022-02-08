(* Copyright (c) 2008, Adam Chlipala
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

Require Import List.

Set Implicit Arguments.


Section ctxt1.
  Variable type : Type.
  Variable var : type -> Type.

  Definition ctxt1 := list (sigT var).
  Definition var1 := existT var.
End ctxt1.

Implicit Arguments ctxt1 [type].
Implicit Arguments var1 [type var x].

Section ctxt.
  Variable type : Type.
  Variables var1 var2 : type -> Type.

  Definition ctxt := list { t : type & (var1 t * var2 t)%type }.
  Definition vars := existT (fun t => (var1 t * var2 t)%type).
End ctxt.

Implicit Arguments vars [type var1 var2 x].

Section ctxt2.
  Variable type : Type -> Type.
  Variables tvar1 tvar2 : Type.
  Variable var1 : type tvar1 -> Type.
  Variable var2 : type tvar2 -> Type.

  Definition ctxt2 := list (sigT var1 * sigT var2).
  Definition vars2 t1 t2 (v1 : var1 t1) (v2 : var2 t2) := (existT _ t1 v1, existT _ t2 v2).
End ctxt2.

Implicit Arguments ctxt2 [type tvar1 tvar2].
Implicit Arguments vars2 [type tvar1 tvar2 var1 var2 t1 t2].

Section ctxt3.
  Variable type : Type -> Type.
  Variables tvar1 tvar2 tvar3 : Type.
  Variable var1 : type tvar1 -> Type.
  Variable var2 : type tvar2 -> Type.
  Variable var3 : type tvar3 -> Type.

  Definition ctxt3 := list (sigT var1 * sigT var2 * sigT var3).
  Definition vars3 t1 t2 t3 (v1 : var1 t1) (v2 : var2 t2) (v3 : var3 t3) :=
    (existT _ t1 v1, existT _ t2 v2, existT _ t3 v3).
End ctxt3.

Implicit Arguments ctxt3 [type tvar1 tvar2 tvar3].
Implicit Arguments vars3 [type tvar1 tvar2 tvar3 var1 var2 var3 t1 t2 t3].
