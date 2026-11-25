{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

module Examples.Voevodsky where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import Agda.Builtin.String

open import CType2
import CType1 as GR
open import GraphForest
open import ImageMatching
open import ImageMorse


voevodsky : List String
voevodsky =
    "                   ######################                       "
  ∷ "                  #######################                       "
  ∷ "                ###########################  ##                 "
  ∷ "               #################################                "
  ∷ "              ###################################               "
  ∷ "             ########################################           "
  ∷ "           ##########################################           "
  ∷ "          #############################################         "
  ∷ "        #################################################       "
  ∷ "        #################################################       "
  ∷ "       ################   #################################     "
  ∷ "      #############      ###################### #############   "
  ∷ "      #############      #####################   ############   "
  ∷ "    #############          ################        ##########   "
  ∷ "    ############           ################        ##########   "
  ∷ "    ###########          #########   ######        ##########   "
  ∷ "  ############         ########     ###  #          ########### "
  ∷ "  ###########          #######     ###   #           ########## "
  ∷ "  ##########           ####       ###                ########## "
  ∷ "  #########                      ##                  ########## "
  ∷ "  #########                     ##                   ########## "
  ∷ "  ########                       #                     ######## "
  ∷ "  ########                                             ######## "
  ∷ "##########                                             ######## "
  ∷ "##########                                             ######## "
  ∷ "##########                                             ######## "
  ∷ "#########                                              ######## "
  ∷ "########                                               ######## "
  ∷ "########                                               ######## "
  ∷ "##    ##                                               ######   "
  ∷ "##    ##                                              #######   "
  ∷ "    ####           ##########            #######     ########   "
  ∷ "      ##                 #####       ########      ########     "
  ∷ "                         #####       ########     #########     "
  ∷ "                 #############     ########################     "
  ∷ "                 # ###########     ########################     "
  ∷ "                         ###       #### ###   ############      "
  ∷ "                                   ##                 ###       "
  ∷ "                                   ##                 ###       "
  ∷ "                                   ##                ###        "
  ∷ "                                   ##                ##         "
  ∷ "                                   ##                ##         "
  ∷ "                                   ####              ##         "
  ∷ "                         ##        ####              ##         "
  ∷ "                       ###         ##  #            ###         "
  ∷ "                   ######              ##          ####         "
  ∷ "                   ####     #        #####        ####          "
  ∷ "                 #####       ##   #######  ####  #####          "
  ∷ "                  ####       ############  ####  ####           "
  ∷ "                     ######   #############      ####           "
  ∷ "                           ################      ##             "
  ∷ "                           ################     ###             "
  ∷ "                                ##########     ###              "
  ∷ "             #                 ##########      ###              "
  ∷ "             ##               ##   ######     ####              "
  ∷ "             ####                           #####               "
  ∷ "             ####                          ###                  "
  ∷ "               ##                        #####                  "
  ∷ "                #####                  #####                    "
  ∷ "                 ####                  ####                     "
  ∷ "                    #####            ####                       "
  ∷ "                    ###################                         "
  ∷ "                     #################                          "
  ∷ "                                                                "
  ∷ []




open Forest voevodsky

--------------------------------------------------------------------------------
-- The Morse complex, written out
--
-- One constructor per Critical vertex and one per Critical edge.  `Arr i j`
-- says that the Critical edge runs from the Critical vertex `i` — the one the
-- edge's source flows to — to `j`, the one its target flows to.

data Vtx : Type where
  v0 v1 v2 v3 v4 v5 v6 v7 : Vtx
  v8 v9 v10 v11 v12 v13 v14 v15 : Vtx
  v16 v17 v18 v19 v20 v21 v22 v23 : Vtx
  v24 v25 v26 v27 v28 v29 v30 v31 : Vtx
  v32 v33 v34 v35 v36 v37 v38 v39 : Vtx
  v40 v41 v42 v43 v44 v45 v46 v47 : Vtx
  v48 v49 v50 v51 v52 v53 v54 v55 : Vtx
  v56 v57 v58 v59 v60 : Vtx

data Arr : Vtx → Vtx → Type where
  a0 : Arr v0 v17
  a1 : Arr v2 v0
  a2 : Arr v1 v42
  a3 : Arr v3 v1
  a4 : Arr v4 v2
  a5 : Arr v8 v3
  a6 : Arr v5 v4
  a7 : Arr v6 v5
  a8 : Arr v7 v18
  a9 : Arr v9 v6
  a10 : Arr v10 v7
  a11 : Arr v11 v15
  a12 : Arr v15 v8
  a13 : Arr v12 v9
  a14 : Arr v13 v10
  a15 : Arr v14 v11
  a16 : Arr v16 v12
  a17 : Arr v17 v13
  a18 : Arr v18 v14
  a19 : Arr v20 v16
  a20 : Arr v19 v18
  a21 : Arr v21 v19
  a22 : Arr v22 v20
  a23 : Arr v23 v22
  a24 : Arr v28 v23
  a25 : Arr v25 v28
  a26 : Arr v27 v24
  a27 : Arr v45 v26
  a28 : Arr v31 v27
  a29 : Arr v29 v32
  a30 : Arr v32 v30
  a31 : Arr v33 v34
  a32 : Arr v34 v45
  a33 : Arr v35 v31
  a34 : Arr v40 v33
  a35 : Arr v36 v35
  a36 : Arr v37 v36
  a37 : Arr v42 v37
  a38 : Arr v39 v38
  a39 : Arr v40 v52
  a40 : Arr v41 v39
  a41 : Arr v43 v41
  a42 : Arr v45 v42
  a43 : Arr v51 v43
  a44 : Arr v52 v44
  a45 : Arr v47 v45
  a46 : Arr v48 v46
  a47 : Arr v49 v47
  a48 : Arr v50 v48
  a49 : Arr v53 v49
  a50 : Arr v52 v50
  a51 : Arr v51 v52
  a52 : Arr v54 v53
  a53 : Arr v55 v54
  a54 : Arr v56 v55
  a55 : Arr v57 v56
  a56 : Arr v58 v57
  a57 : Arr v59 v58
  a58 : Arr v60 v59

--------------------------------------------------------------------------------
-- It is a forest, and its realisation is therefore its set of components
--
-- The two roots, a path from each vertex to the root of its component running
-- up the forest, and — for every edge — the triangle those paths span.  A
-- child's path is by construction its parent's followed by the edge between
-- them, so the triangles are all `compPath-filler`.

ι : Bool → Vtx
ι false = v0
ι true  = v29

q0 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v0 ∣₀)
q0 = refl
q17 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v17 ∣₀)
q17 = q0 ∙ GR.∣ v0 ⇒ v17 ∋ a0 ∣₁
q2 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v2 ∣₀)
q2 = q0 ∙ sym GR.∣ v2 ⇒ v0 ∋ a1 ∣₁
q13 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v13 ∣₀)
q13 = q17 ∙ GR.∣ v17 ⇒ v13 ∋ a17 ∣₁
q4 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v4 ∣₀)
q4 = q2 ∙ sym GR.∣ v4 ⇒ v2 ∋ a4 ∣₁
q10 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v10 ∣₀)
q10 = q13 ∙ GR.∣ v13 ⇒ v10 ∋ a14 ∣₁
q5 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v5 ∣₀)
q5 = q4 ∙ sym GR.∣ v5 ⇒ v4 ∋ a6 ∣₁
q7 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v7 ∣₀)
q7 = q10 ∙ GR.∣ v10 ⇒ v7 ∋ a10 ∣₁
q6 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v6 ∣₀)
q6 = q5 ∙ sym GR.∣ v6 ⇒ v5 ∋ a7 ∣₁
q18 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v18 ∣₀)
q18 = q7 ∙ GR.∣ v7 ⇒ v18 ∋ a8 ∣₁
q9 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v9 ∣₀)
q9 = q6 ∙ sym GR.∣ v9 ⇒ v6 ∋ a9 ∣₁
q14 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v14 ∣₀)
q14 = q18 ∙ GR.∣ v18 ⇒ v14 ∋ a18 ∣₁
q19 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v19 ∣₀)
q19 = q18 ∙ sym GR.∣ v19 ⇒ v18 ∋ a20 ∣₁
q12 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v12 ∣₀)
q12 = q9 ∙ sym GR.∣ v12 ⇒ v9 ∋ a13 ∣₁
q11 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v11 ∣₀)
q11 = q14 ∙ GR.∣ v14 ⇒ v11 ∋ a15 ∣₁
q21 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v21 ∣₀)
q21 = q19 ∙ sym GR.∣ v21 ⇒ v19 ∋ a21 ∣₁
q16 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v16 ∣₀)
q16 = q12 ∙ sym GR.∣ v16 ⇒ v12 ∋ a16 ∣₁
q15 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v15 ∣₀)
q15 = q11 ∙ GR.∣ v11 ⇒ v15 ∋ a11 ∣₁
q20 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v20 ∣₀)
q20 = q16 ∙ sym GR.∣ v20 ⇒ v16 ∋ a19 ∣₁
q8 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v8 ∣₀)
q8 = q15 ∙ GR.∣ v15 ⇒ v8 ∋ a12 ∣₁
q22 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v22 ∣₀)
q22 = q20 ∙ sym GR.∣ v22 ⇒ v20 ∋ a22 ∣₁
q3 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v3 ∣₀)
q3 = q8 ∙ GR.∣ v8 ⇒ v3 ∋ a5 ∣₁
q23 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v23 ∣₀)
q23 = q22 ∙ sym GR.∣ v23 ⇒ v22 ∋ a23 ∣₁
q1 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v1 ∣₀)
q1 = q3 ∙ GR.∣ v3 ⇒ v1 ∋ a3 ∣₁
q28 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v28 ∣₀)
q28 = q23 ∙ sym GR.∣ v28 ⇒ v23 ∋ a24 ∣₁
q42 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v42 ∣₀)
q42 = q1 ∙ GR.∣ v1 ⇒ v42 ∋ a2 ∣₁
q25 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v25 ∣₀)
q25 = q28 ∙ sym GR.∣ v25 ⇒ v28 ∋ a25 ∣₁
q37 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v37 ∣₀)
q37 = q42 ∙ GR.∣ v42 ⇒ v37 ∋ a37 ∣₁
q45 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v45 ∣₀)
q45 = q42 ∙ sym GR.∣ v45 ⇒ v42 ∋ a42 ∣₁
q36 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v36 ∣₀)
q36 = q37 ∙ GR.∣ v37 ⇒ v36 ∋ a36 ∣₁
q26 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v26 ∣₀)
q26 = q45 ∙ GR.∣ v45 ⇒ v26 ∋ a27 ∣₁
q34 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v34 ∣₀)
q34 = q45 ∙ sym GR.∣ v34 ⇒ v45 ∋ a32 ∣₁
q47 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v47 ∣₀)
q47 = q45 ∙ sym GR.∣ v47 ⇒ v45 ∋ a45 ∣₁
q35 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v35 ∣₀)
q35 = q36 ∙ GR.∣ v36 ⇒ v35 ∋ a35 ∣₁
q33 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v33 ∣₀)
q33 = q34 ∙ sym GR.∣ v33 ⇒ v34 ∋ a31 ∣₁
q49 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v49 ∣₀)
q49 = q47 ∙ sym GR.∣ v49 ⇒ v47 ∋ a47 ∣₁
q31 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v31 ∣₀)
q31 = q35 ∙ GR.∣ v35 ⇒ v31 ∋ a33 ∣₁
q40 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v40 ∣₀)
q40 = q33 ∙ sym GR.∣ v40 ⇒ v33 ∋ a34 ∣₁
q53 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v53 ∣₀)
q53 = q49 ∙ sym GR.∣ v53 ⇒ v49 ∋ a49 ∣₁
q27 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v27 ∣₀)
q27 = q31 ∙ GR.∣ v31 ⇒ v27 ∋ a28 ∣₁
q52 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v52 ∣₀)
q52 = q40 ∙ GR.∣ v40 ⇒ v52 ∋ a39 ∣₁
q54 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v54 ∣₀)
q54 = q53 ∙ sym GR.∣ v54 ⇒ v53 ∋ a52 ∣₁
q24 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v24 ∣₀)
q24 = q27 ∙ GR.∣ v27 ⇒ v24 ∋ a26 ∣₁
q44 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v44 ∣₀)
q44 = q52 ∙ GR.∣ v52 ⇒ v44 ∋ a44 ∣₁
q50 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v50 ∣₀)
q50 = q52 ∙ GR.∣ v52 ⇒ v50 ∋ a50 ∣₁
q51 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v51 ∣₀)
q51 = q52 ∙ sym GR.∣ v51 ⇒ v52 ∋ a51 ∣₁
q55 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v55 ∣₀)
q55 = q54 ∙ sym GR.∣ v55 ⇒ v54 ∋ a53 ∣₁
q48 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v48 ∣₀)
q48 = q50 ∙ GR.∣ v50 ⇒ v48 ∋ a48 ∣₁
q43 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v43 ∣₀)
q43 = q51 ∙ GR.∣ v51 ⇒ v43 ∋ a43 ∣₁
q56 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v56 ∣₀)
q56 = q55 ∙ sym GR.∣ v56 ⇒ v55 ∋ a54 ∣₁
q46 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v46 ∣₀)
q46 = q48 ∙ GR.∣ v48 ⇒ v46 ∋ a46 ∣₁
q41 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v41 ∣₀)
q41 = q43 ∙ GR.∣ v43 ⇒ v41 ∋ a41 ∣₁
q57 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v57 ∣₀)
q57 = q56 ∙ sym GR.∣ v57 ⇒ v56 ∋ a55 ∣₁
q39 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v39 ∣₀)
q39 = q41 ∙ GR.∣ v41 ⇒ v39 ∋ a40 ∣₁
q58 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v58 ∣₀)
q58 = q57 ∙ sym GR.∣ v58 ⇒ v57 ∋ a56 ∣₁
q38 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v38 ∣₀)
q38 = q39 ∙ GR.∣ v39 ⇒ v38 ∋ a38 ∣₁
q59 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v59 ∣₀)
q59 = q58 ∙ sym GR.∣ v59 ⇒ v58 ∋ a57 ∣₁
q60 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι false ∣₀) (GR.∣ v60 ∣₀)
q60 = q59 ∙ sym GR.∣ v60 ⇒ v59 ∋ a58 ∣₁
q29 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι true ∣₀) (GR.∣ v29 ∣₀)
q29 = refl
q32 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι true ∣₀) (GR.∣ v32 ∣₀)
q32 = q29 ∙ GR.∣ v29 ⇒ v32 ∋ a29 ∣₁
q30 : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι true ∣₀) (GR.∣ v30 ∣₀)
q30 = q32 ∙ GR.∣ v32 ⇒ v30 ∋ a30 ∣₁

-- which component a vertex lives in: v29, v30 and v32 hang off the second
-- root, everything else off the first
root : Vtx → Bool
root v29 = true
root v30 = true
root v32 = true
root _   = false

rootIsRoot : (r : Bool) → root (ι r) ≡ r
rootIsRoot false = refl
rootIsRoot true  = refl

rootPath : (v : Vtx) → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (root v) ∣₀) (GR.∣ v ∣₀)
rootPath v0 = q0
rootPath v1 = q1
rootPath v2 = q2
rootPath v3 = q3
rootPath v4 = q4
rootPath v5 = q5
rootPath v6 = q6
rootPath v7 = q7
rootPath v8 = q8
rootPath v9 = q9
rootPath v10 = q10
rootPath v11 = q11
rootPath v12 = q12
rootPath v13 = q13
rootPath v14 = q14
rootPath v15 = q15
rootPath v16 = q16
rootPath v17 = q17
rootPath v18 = q18
rootPath v19 = q19
rootPath v20 = q20
rootPath v21 = q21
rootPath v22 = q22
rootPath v23 = q23
rootPath v24 = q24
rootPath v25 = q25
rootPath v26 = q26
rootPath v27 = q27
rootPath v28 = q28
rootPath v29 = q29
rootPath v30 = q30
rootPath v31 = q31
rootPath v32 = q32
rootPath v33 = q33
rootPath v34 = q34
rootPath v35 = q35
rootPath v36 = q36
rootPath v37 = q37
rootPath v38 = q38
rootPath v39 = q39
rootPath v40 = q40
rootPath v41 = q41
rootPath v42 = q42
rootPath v43 = q43
rootPath v44 = q44
rootPath v45 = q45
rootPath v46 = q46
rootPath v47 = q47
rootPath v48 = q48
rootPath v49 = q49
rootPath v50 = q50
rootPath v51 = q51
rootPath v52 = q52
rootPath v53 = q53
rootPath v54 = q54
rootPath v55 = q55
rootPath v56 = q56
rootPath v57 = q57
rootPath v58 = q58
rootPath v59 = q59
rootPath v60 = q60

contrEdge : {i j : Vtx} (a : Arr i j)
  → Σ[ α ∈ root i ≡ root j ]
      PathP (λ k → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (α k) ∣₀) (GR.∣ i ⇒ j ∋ a ∣₁ k))
            (rootPath i) (rootPath j)
contrEdge a0 = refl , compPath-filler q0 GR.∣ v0 ⇒ v17 ∋ a0 ∣₁
contrEdge a1 = refl , symP (compPath-filler q0 (sym GR.∣ v2 ⇒ v0 ∋ a1 ∣₁))
contrEdge a17 = refl , compPath-filler q17 GR.∣ v17 ⇒ v13 ∋ a17 ∣₁
contrEdge a4 = refl , symP (compPath-filler q2 (sym GR.∣ v4 ⇒ v2 ∋ a4 ∣₁))
contrEdge a14 = refl , compPath-filler q13 GR.∣ v13 ⇒ v10 ∋ a14 ∣₁
contrEdge a6 = refl , symP (compPath-filler q4 (sym GR.∣ v5 ⇒ v4 ∋ a6 ∣₁))
contrEdge a10 = refl , compPath-filler q10 GR.∣ v10 ⇒ v7 ∋ a10 ∣₁
contrEdge a7 = refl , symP (compPath-filler q5 (sym GR.∣ v6 ⇒ v5 ∋ a7 ∣₁))
contrEdge a8 = refl , compPath-filler q7 GR.∣ v7 ⇒ v18 ∋ a8 ∣₁
contrEdge a9 = refl , symP (compPath-filler q6 (sym GR.∣ v9 ⇒ v6 ∋ a9 ∣₁))
contrEdge a18 = refl , compPath-filler q18 GR.∣ v18 ⇒ v14 ∋ a18 ∣₁
contrEdge a20 = refl , symP (compPath-filler q18 (sym GR.∣ v19 ⇒ v18 ∋ a20 ∣₁))
contrEdge a13 = refl , symP (compPath-filler q9 (sym GR.∣ v12 ⇒ v9 ∋ a13 ∣₁))
contrEdge a15 = refl , compPath-filler q14 GR.∣ v14 ⇒ v11 ∋ a15 ∣₁
contrEdge a21 = refl , symP (compPath-filler q19 (sym GR.∣ v21 ⇒ v19 ∋ a21 ∣₁))
contrEdge a16 = refl , symP (compPath-filler q12 (sym GR.∣ v16 ⇒ v12 ∋ a16 ∣₁))
contrEdge a11 = refl , compPath-filler q11 GR.∣ v11 ⇒ v15 ∋ a11 ∣₁
contrEdge a19 = refl , symP (compPath-filler q16 (sym GR.∣ v20 ⇒ v16 ∋ a19 ∣₁))
contrEdge a12 = refl , compPath-filler q15 GR.∣ v15 ⇒ v8 ∋ a12 ∣₁
contrEdge a22 = refl , symP (compPath-filler q20 (sym GR.∣ v22 ⇒ v20 ∋ a22 ∣₁))
contrEdge a5 = refl , compPath-filler q8 GR.∣ v8 ⇒ v3 ∋ a5 ∣₁
contrEdge a23 = refl , symP (compPath-filler q22 (sym GR.∣ v23 ⇒ v22 ∋ a23 ∣₁))
contrEdge a3 = refl , compPath-filler q3 GR.∣ v3 ⇒ v1 ∋ a3 ∣₁
contrEdge a24 = refl , symP (compPath-filler q23 (sym GR.∣ v28 ⇒ v23 ∋ a24 ∣₁))
contrEdge a2 = refl , compPath-filler q1 GR.∣ v1 ⇒ v42 ∋ a2 ∣₁
contrEdge a25 = refl , symP (compPath-filler q28 (sym GR.∣ v25 ⇒ v28 ∋ a25 ∣₁))
contrEdge a37 = refl , compPath-filler q42 GR.∣ v42 ⇒ v37 ∋ a37 ∣₁
contrEdge a42 = refl , symP (compPath-filler q42 (sym GR.∣ v45 ⇒ v42 ∋ a42 ∣₁))
contrEdge a36 = refl , compPath-filler q37 GR.∣ v37 ⇒ v36 ∋ a36 ∣₁
contrEdge a27 = refl , compPath-filler q45 GR.∣ v45 ⇒ v26 ∋ a27 ∣₁
contrEdge a32 = refl , symP (compPath-filler q45 (sym GR.∣ v34 ⇒ v45 ∋ a32 ∣₁))
contrEdge a45 = refl , symP (compPath-filler q45 (sym GR.∣ v47 ⇒ v45 ∋ a45 ∣₁))
contrEdge a35 = refl , compPath-filler q36 GR.∣ v36 ⇒ v35 ∋ a35 ∣₁
contrEdge a31 = refl , symP (compPath-filler q34 (sym GR.∣ v33 ⇒ v34 ∋ a31 ∣₁))
contrEdge a47 = refl , symP (compPath-filler q47 (sym GR.∣ v49 ⇒ v47 ∋ a47 ∣₁))
contrEdge a33 = refl , compPath-filler q35 GR.∣ v35 ⇒ v31 ∋ a33 ∣₁
contrEdge a34 = refl , symP (compPath-filler q33 (sym GR.∣ v40 ⇒ v33 ∋ a34 ∣₁))
contrEdge a49 = refl , symP (compPath-filler q49 (sym GR.∣ v53 ⇒ v49 ∋ a49 ∣₁))
contrEdge a28 = refl , compPath-filler q31 GR.∣ v31 ⇒ v27 ∋ a28 ∣₁
contrEdge a39 = refl , compPath-filler q40 GR.∣ v40 ⇒ v52 ∋ a39 ∣₁
contrEdge a52 = refl , symP (compPath-filler q53 (sym GR.∣ v54 ⇒ v53 ∋ a52 ∣₁))
contrEdge a26 = refl , compPath-filler q27 GR.∣ v27 ⇒ v24 ∋ a26 ∣₁
contrEdge a44 = refl , compPath-filler q52 GR.∣ v52 ⇒ v44 ∋ a44 ∣₁
contrEdge a50 = refl , compPath-filler q52 GR.∣ v52 ⇒ v50 ∋ a50 ∣₁
contrEdge a51 = refl , symP (compPath-filler q52 (sym GR.∣ v51 ⇒ v52 ∋ a51 ∣₁))
contrEdge a53 = refl , symP (compPath-filler q54 (sym GR.∣ v55 ⇒ v54 ∋ a53 ∣₁))
contrEdge a48 = refl , compPath-filler q50 GR.∣ v50 ⇒ v48 ∋ a48 ∣₁
contrEdge a43 = refl , compPath-filler q51 GR.∣ v51 ⇒ v43 ∋ a43 ∣₁
contrEdge a54 = refl , symP (compPath-filler q55 (sym GR.∣ v56 ⇒ v55 ∋ a54 ∣₁))
contrEdge a46 = refl , compPath-filler q48 GR.∣ v48 ⇒ v46 ∋ a46 ∣₁
contrEdge a41 = refl , compPath-filler q43 GR.∣ v43 ⇒ v41 ∋ a41 ∣₁
contrEdge a55 = refl , symP (compPath-filler q56 (sym GR.∣ v57 ⇒ v56 ∋ a55 ∣₁))
contrEdge a40 = refl , compPath-filler q41 GR.∣ v41 ⇒ v39 ∋ a40 ∣₁
contrEdge a56 = refl , symP (compPath-filler q57 (sym GR.∣ v58 ⇒ v57 ∋ a56 ∣₁))
contrEdge a38 = refl , compPath-filler q39 GR.∣ v39 ⇒ v38 ∋ a38 ∣₁
contrEdge a57 = refl , symP (compPath-filler q58 (sym GR.∣ v59 ⇒ v58 ∋ a57 ∣₁))
contrEdge a58 = refl , symP (compPath-filler q59 (sym GR.∣ v60 ⇒ v59 ∋ a58 ∣₁))
contrEdge a29 = refl , compPath-filler q29 GR.∣ v29 ⇒ v32 ∋ a29 ∣₁
contrEdge a30 = refl , compPath-filler q32 GR.∣ v32 ⇒ v30 ∋ a30 ∣₁

isPropArr : (i j : Vtx) → isHProp (Arr i j)
isPropArr v0 v17 a0 a0 = refl
isPropArr v2 v0 a1 a1 = refl
isPropArr v1 v42 a2 a2 = refl
isPropArr v3 v1 a3 a3 = refl
isPropArr v4 v2 a4 a4 = refl
isPropArr v8 v3 a5 a5 = refl
isPropArr v5 v4 a6 a6 = refl
isPropArr v6 v5 a7 a7 = refl
isPropArr v7 v18 a8 a8 = refl
isPropArr v9 v6 a9 a9 = refl
isPropArr v10 v7 a10 a10 = refl
isPropArr v11 v15 a11 a11 = refl
isPropArr v15 v8 a12 a12 = refl
isPropArr v12 v9 a13 a13 = refl
isPropArr v13 v10 a14 a14 = refl
isPropArr v14 v11 a15 a15 = refl
isPropArr v16 v12 a16 a16 = refl
isPropArr v17 v13 a17 a17 = refl
isPropArr v18 v14 a18 a18 = refl
isPropArr v20 v16 a19 a19 = refl
isPropArr v19 v18 a20 a20 = refl
isPropArr v21 v19 a21 a21 = refl
isPropArr v22 v20 a22 a22 = refl
isPropArr v23 v22 a23 a23 = refl
isPropArr v28 v23 a24 a24 = refl
isPropArr v25 v28 a25 a25 = refl
isPropArr v27 v24 a26 a26 = refl
isPropArr v45 v26 a27 a27 = refl
isPropArr v31 v27 a28 a28 = refl
isPropArr v29 v32 a29 a29 = refl
isPropArr v32 v30 a30 a30 = refl
isPropArr v33 v34 a31 a31 = refl
isPropArr v34 v45 a32 a32 = refl
isPropArr v35 v31 a33 a33 = refl
isPropArr v40 v33 a34 a34 = refl
isPropArr v36 v35 a35 a35 = refl
isPropArr v37 v36 a36 a36 = refl
isPropArr v42 v37 a37 a37 = refl
isPropArr v39 v38 a38 a38 = refl
isPropArr v40 v52 a39 a39 = refl
isPropArr v41 v39 a40 a40 = refl
isPropArr v43 v41 a41 a41 = refl
isPropArr v45 v42 a42 a42 = refl
isPropArr v51 v43 a43 a43 = refl
isPropArr v52 v44 a44 a44 = refl
isPropArr v47 v45 a45 a45 = refl
isPropArr v48 v46 a46 a46 = refl
isPropArr v49 v47 a47 a47 = refl
isPropArr v50 v48 a48 a48 = refl
isPropArr v53 v49 a49 a49 = refl
isPropArr v52 v50 a50 a50 = refl
isPropArr v51 v52 a51 a51 = refl
isPropArr v54 v53 a52 a52 = refl
isPropArr v55 v54 a53 a53 = refl
isPropArr v56 v55 a54 a54 = refl
isPropArr v57 v56 a55 a55 = refl
isPropArr v58 v57 a56 a56 = refl
isPropArr v59 v58 a57 a57 = refl
isPropArr v60 v59 a58 a58 = refl

∣Arr∣≡Bool : GR.∣ Vtx , Arr ∣ ≡ Bool
∣Arr∣≡Bool = ForestCollapse Bool ι root rootIsRoot rootPath contrEdge

--------------------------------------------------------------------------------
-- … and it is the Morse complex of the picture
--
-- `G` sends a vertex of the graph above to the Critical vertex it names — the
-- sink of the gradient flow at that position — and `F` looks a position up in
-- the table.  Every clause of `S` is a `refl`: the flow computes.

CritAt : (x y : ℕ) {h : Bool→Type (vertexB x y)} → Mo.Crit₀
CritAt x y {h} = Mo.sink ((x , y) , h)

G : Vtx → Mo.Crit₀
G v0 = CritAt 23 11
G v1 = CritAt 47 12
G v2 = CritAt 19 13
G v3 = CritAt 46 13
G v4 = CritAt 17 14
G v5 = CritAt 16 15
G v6 = CritAt 15 16
G v7 = CritAt 34 16
G v8 = CritAt 43 16
G v9 = CritAt 14 17
G v10 = CritAt 31 17
G v11 = CritAt 39 17
G v12 = CritAt 13 18
G v13 = CritAt 30 18
G v14 = CritAt 38 18
G v15 = CritAt 42 18
G v16 = CritAt 12 19
G v17 = CritAt 27 19
G v18 = CritAt 37 19
G v19 = CritAt 35 20
G v20 = CritAt 11 21
G v21 = CritAt 34 22
G v22 = CritAt 10 26
G v23 = CritAt 9 27
G v24 = CritAt 63 29
G v25 = CritAt 2 31
G v26 = CritAt 48 32
G v27 = CritAt 61 32
G v28 = CritAt 8 33
G v29 = CritAt 18 36
G v30 = CritAt 30 36
G v31 = CritAt 59 36
G v32 = CritAt 28 37
G v33 = CritAt 39 37
G v34 = CritAt 43 37
G v35 = CritAt 58 37
G v36 = CritAt 57 39
G v37 = CritAt 56 40
G v38 = CritAt 27 44
G v39 = CritAt 26 45
G v40 = CritAt 37 45
G v41 = CritAt 25 46
G v42 = CritAt 55 46
G v43 = CritAt 23 47
G v44 = CritAt 42 47
G v45 = CritAt 54 48
G v46 = CritAt 47 49
G v47 = CritAt 53 50
G v48 = CritAt 43 52
G v49 = CritAt 51 52
G v50 = CritAt 42 53
G v51 = CritAt 32 55
G v52 = CritAt 41 55
G v53 = CritAt 50 55
G v54 = CritAt 49 56
G v55 = CritAt 46 58
G v56 = CritAt 44 59
G v57 = CritAt 43 60
G v58 = CritAt 41 61
G v59 = CritAt 39 62
G v60 = CritAt 38 63

vtxTable : List ((ℕ × ℕ) × Vtx)
vtxTable =
      ((23 , 11) , v0)
    ∷ ((47 , 12) , v1)
    ∷ ((19 , 13) , v2)
    ∷ ((46 , 13) , v3)
    ∷ ((17 , 14) , v4)
    ∷ ((16 , 15) , v5)
    ∷ ((15 , 16) , v6)
    ∷ ((34 , 16) , v7)
    ∷ ((43 , 16) , v8)
    ∷ ((14 , 17) , v9)
    ∷ ((31 , 17) , v10)
    ∷ ((39 , 17) , v11)
    ∷ ((13 , 18) , v12)
    ∷ ((30 , 18) , v13)
    ∷ ((38 , 18) , v14)
    ∷ ((42 , 18) , v15)
    ∷ ((12 , 19) , v16)
    ∷ ((27 , 19) , v17)
    ∷ ((37 , 19) , v18)
    ∷ ((35 , 20) , v19)
    ∷ ((11 , 21) , v20)
    ∷ ((34 , 22) , v21)
    ∷ ((10 , 26) , v22)
    ∷ ((9 , 27) , v23)
    ∷ ((63 , 29) , v24)
    ∷ ((2 , 31) , v25)
    ∷ ((48 , 32) , v26)
    ∷ ((61 , 32) , v27)
    ∷ ((8 , 33) , v28)
    ∷ ((18 , 36) , v29)
    ∷ ((30 , 36) , v30)
    ∷ ((59 , 36) , v31)
    ∷ ((28 , 37) , v32)
    ∷ ((39 , 37) , v33)
    ∷ ((43 , 37) , v34)
    ∷ ((58 , 37) , v35)
    ∷ ((57 , 39) , v36)
    ∷ ((56 , 40) , v37)
    ∷ ((27 , 44) , v38)
    ∷ ((26 , 45) , v39)
    ∷ ((37 , 45) , v40)
    ∷ ((25 , 46) , v41)
    ∷ ((55 , 46) , v42)
    ∷ ((23 , 47) , v43)
    ∷ ((42 , 47) , v44)
    ∷ ((54 , 48) , v45)
    ∷ ((47 , 49) , v46)
    ∷ ((53 , 50) , v47)
    ∷ ((43 , 52) , v48)
    ∷ ((51 , 52) , v49)
    ∷ ((42 , 53) , v50)
    ∷ ((32 , 55) , v51)
    ∷ ((41 , 55) , v52)
    ∷ ((50 , 55) , v53)
    ∷ ((49 , 56) , v54)
    ∷ ((46 , 58) , v55)
    ∷ ((44 , 59) , v56)
    ∷ ((43 , 60) , v57)
    ∷ ((41 , 61) , v58)
    ∷ ((39 , 62) , v59)
    ∷ ((38 , 63) , v60)
  ∷ []

lookupVtx : ℕ → ℕ → List ((ℕ × ℕ) × Vtx) → Vtx
lookupVtx x y []                 = v0
lookupVtx x y (((a , b) , w) ∷ t) =
  if (eqℕ x a and eqℕ y b) then w else lookupVtx x y t

F : Mo.Crit₀ → Vtx
F c = lookupVtx (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) vtxTable

S : (v : Vtx) → F (G v) ≡ v
S v0 = refl
S v1 = refl
S v2 = refl
S v3 = refl
S v4 = refl
S v5 = refl
S v6 = refl
S v7 = refl
S v8 = refl
S v9 = refl
S v10 = refl
S v11 = refl
S v12 = refl
S v13 = refl
S v14 = refl
S v15 = refl
S v16 = refl
S v17 = refl
S v18 = refl
S v19 = refl
S v20 = refl
S v21 = refl
S v22 = refl
S v23 = refl
S v24 = refl
S v25 = refl
S v26 = refl
S v27 = refl
S v28 = refl
S v29 = refl
S v30 = refl
S v31 = refl
S v32 = refl
S v33 = refl
S v34 = refl
S v35 = refl
S v36 = refl
S v37 = refl
S v38 = refl
S v39 = refl
S v40 = refl
S v41 = refl
S v42 = refl
S v43 = refl
S v44 = refl
S v45 = refl
S v46 = refl
S v47 = refl
S v48 = refl
S v49 = refl
S v50 = refl
S v51 = refl
S v52 = refl
S v53 = refl
S v54 = refl
S v55 = refl
S v56 = refl
S v57 = refl
S v58 = refl
S v59 = refl
S v60 = refl

G₁ : (i j : Vtx) → Arr i j → Mo⁻.Crit₁ (G i) (G j)
G₁ v0 v17 a0 = arrAt 23 10
G₁ v2 v0 a1 = arrAt 19 11
G₁ v1 v42 a2 = arrAt 47 11
G₁ v3 v1 a3 = arrAt 46 12
G₁ v4 v2 a4 = arrAt 17 13
G₁ v8 v3 a5 = arrAt 43 13
G₁ v5 v4 a6 = arrAt 16 14
G₁ v6 v5 a7 = arrAt 15 15
G₁ v7 v18 a8 = arrAt 34 15
G₁ v9 v6 a9 = arrAt 14 16
G₁ v10 v7 a10 = arrAt 31 16
G₁ v11 v15 a11 = arrAt 39 16
G₁ v15 v8 a12 = arrAt 42 16
G₁ v12 v9 a13 = arrAt 13 17
G₁ v13 v10 a14 = arrAt 30 17
G₁ v14 v11 a15 = arrAt 38 17
G₁ v16 v12 a16 = arrAt 12 18
G₁ v17 v13 a17 = arrAt 27 18
G₁ v18 v14 a18 = arrAt 37 18
G₁ v20 v16 a19 = arrAt 11 19
G₁ v19 v18 a20 = arrAt 35 19
G₁ v21 v19 a21 = arrAt 34 20
G₁ v22 v20 a22 = arrAt 10 21
G₁ v23 v22 a23 = arrAt 9 26
G₁ v28 v23 a24 = arrAt 8 27
G₁ v25 v28 a25 = arrAt 2 29
G₁ v27 v24 a26 = arrAt 61 29
G₁ v45 v26 a27 = arrAt 45 32
G₁ v31 v27 a28 = arrAt 59 32
G₁ v29 v32 a29 = arrAt 18 35
G₁ v32 v30 a30 = arrAt 28 36
G₁ v33 v34 a31 = arrAt 39 36
G₁ v34 v45 a32 = arrAt 43 36
G₁ v35 v31 a33 = arrAt 58 36
G₁ v40 v33 a34 = arrAt 37 37
G₁ v36 v35 a35 = arrAt 57 37
G₁ v37 v36 a36 = arrAt 56 39
G₁ v42 v37 a37 = arrAt 55 40
G₁ v39 v38 a38 = arrAt 26 44
G₁ v40 v52 a39 = arrAt 37 44
G₁ v41 v39 a40 = arrAt 25 45
G₁ v43 v41 a41 = arrAt 23 46
G₁ v45 v42 a42 = arrAt 54 46
G₁ v51 v43 a43 = arrAt 22 47
G₁ v52 v44 a44 = arrAt 41 47
G₁ v47 v45 a45 = arrAt 53 48
G₁ v48 v46 a46 = arrAt 43 49
G₁ v49 v47 a47 = arrAt 51 50
G₁ v50 v48 a48 = arrAt 42 52
G₁ v53 v49 a49 = arrAt 50 52
G₁ v52 v50 a50 = arrAt 41 53
G₁ v51 v52 a51 = arrAt 32 54
G₁ v54 v53 a52 = arrAt 49 55
G₁ v55 v54 a53 = arrAt 46 56
G₁ v56 v55 a54 = arrAt 44 58
G₁ v57 v56 a55 = arrAt 43 59
G₁ v58 v57 a56 = arrAt 41 60
G₁ v59 v58 a57 = arrAt 39 61
G₁ v60 v59 a58 = arrAt 38 62

--------------------------------------------------------------------------------
-- Nothing is missing
--
-- A Critical edge of the picture is horizontal, with a white pixel below it
-- and a black one to its south-west; a Critical vertex has neither an edge
-- below it nor a free edge to its right.  Both are boolean conditions, so a
-- single computation over the box the picture lives in checks that the lists
-- above catch every one of them.

CritEdgesB CritVB : ℕ → ℕ → Bool
CritEdgesB x y = hEdgesB x y and (not (black x y) and vEdgesB x y)
CritVB   x y = not (vEdgesB x y) and not (hEdgesB x y and not (black x y))

eList : List (ℕ × ℕ)
eList =
      (23 , 10)
    ∷ (19 , 11)
    ∷ (47 , 11)
    ∷ (46 , 12)
    ∷ (17 , 13)
    ∷ (43 , 13)
    ∷ (16 , 14)
    ∷ (15 , 15)
    ∷ (34 , 15)
    ∷ (14 , 16)
    ∷ (31 , 16)
    ∷ (39 , 16)
    ∷ (42 , 16)
    ∷ (13 , 17)
    ∷ (30 , 17)
    ∷ (38 , 17)
    ∷ (12 , 18)
    ∷ (27 , 18)
    ∷ (37 , 18)
    ∷ (11 , 19)
    ∷ (35 , 19)
    ∷ (34 , 20)
    ∷ (10 , 21)
    ∷ (9 , 26)
    ∷ (8 , 27)
    ∷ (2 , 29)
    ∷ (61 , 29)
    ∷ (45 , 32)
    ∷ (59 , 32)
    ∷ (18 , 35)
    ∷ (28 , 36)
    ∷ (39 , 36)
    ∷ (43 , 36)
    ∷ (58 , 36)
    ∷ (37 , 37)
    ∷ (57 , 37)
    ∷ (56 , 39)
    ∷ (55 , 40)
    ∷ (26 , 44)
    ∷ (37 , 44)
    ∷ (25 , 45)
    ∷ (23 , 46)
    ∷ (54 , 46)
    ∷ (22 , 47)
    ∷ (41 , 47)
    ∷ (53 , 48)
    ∷ (43 , 49)
    ∷ (51 , 50)
    ∷ (42 , 52)
    ∷ (50 , 52)
    ∷ (41 , 53)
    ∷ (32 , 54)
    ∷ (49 , 55)
    ∷ (46 , 56)
    ∷ (44 , 58)
    ∷ (43 , 59)
    ∷ (41 , 60)
    ∷ (39 , 61)
    ∷ (38 , 62)
  ∷ []

vList : List (ℕ × ℕ)
vList =
      (23 , 11)
    ∷ (47 , 12)
    ∷ (19 , 13)
    ∷ (46 , 13)
    ∷ (17 , 14)
    ∷ (16 , 15)
    ∷ (15 , 16)
    ∷ (34 , 16)
    ∷ (43 , 16)
    ∷ (14 , 17)
    ∷ (31 , 17)
    ∷ (39 , 17)
    ∷ (13 , 18)
    ∷ (30 , 18)
    ∷ (38 , 18)
    ∷ (42 , 18)
    ∷ (12 , 19)
    ∷ (27 , 19)
    ∷ (37 , 19)
    ∷ (35 , 20)
    ∷ (11 , 21)
    ∷ (34 , 22)
    ∷ (10 , 26)
    ∷ (9 , 27)
    ∷ (63 , 29)
    ∷ (2 , 31)
    ∷ (48 , 32)
    ∷ (61 , 32)
    ∷ (8 , 33)
    ∷ (18 , 36)
    ∷ (30 , 36)
    ∷ (59 , 36)
    ∷ (28 , 37)
    ∷ (39 , 37)
    ∷ (43 , 37)
    ∷ (58 , 37)
    ∷ (57 , 39)
    ∷ (56 , 40)
    ∷ (27 , 44)
    ∷ (26 , 45)
    ∷ (37 , 45)
    ∷ (25 , 46)
    ∷ (55 , 46)
    ∷ (23 , 47)
    ∷ (42 , 47)
    ∷ (54 , 48)
    ∷ (47 , 49)
    ∷ (53 , 50)
    ∷ (43 , 52)
    ∷ (51 , 52)
    ∷ (42 , 53)
    ∷ (32 , 55)
    ∷ (41 , 55)
    ∷ (50 , 55)
    ∷ (49 , 56)
    ∷ (46 , 58)
    ∷ (44 , 59)
    ∷ (43 , 60)
    ∷ (41 , 61)
    ∷ (39 , 62)
    ∷ (38 , 63)
  ∷ []

eBox : (u : V) → Bool→Type (not (CritEdgesB (fst (pos u)) (snd (pos u)))
                            or memB (fst (pos u)) (snd (pos u)) eList)
eBox = allVertices (λ x y → not (CritEdgesB x y) or memB x y eList) tt

vBox : (u : V) → Bool→Type (not (CritVB (fst (pos u)) (snd (pos u)))
                            or memB (fst (pos u)) (snd (pos u)) vList)
vBox = allVertices (λ x y → not (CritVB x y) or memB x y vList) tt

eMem : {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d)
  → Bool→Type (memB (fst (pos (src (fst f Mo.ₑ)))) (snd (pos (src (fst f Mo.ₑ)))) eList)
eMem ((((x , y) , hu) , v , g , ¬up) , ¬dn , _ , _)
  with CritEdges (((x , y) , hu) , v , g) ¬dn ¬up
... | (h , r , ¬b , vd)
  with or-elim (not (CritEdgesB x y)) (memB x y eList) (eBox ((x , y) , hu))
...   | inl ¬ce = absurd (not-elim (CritEdgesB x y) ¬ce
                    (and-i (hEdgesB x y) (not (black x y) and vEdgesB x y) r
                      (and-i (not (black x y)) (vEdgesB x y) (not-i (black x y) ¬b) vd)))
...   | inr m   = m

vMem : (c : Mo.Crit₀)
  → Bool→Type (memB (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) vList)
vMem (((x , y) , hu) , p) with CritVertex ((x , y) , hu) p
... | (¬d , f)
  with or-elim (not (CritVB x y)) (memB x y vList) (vBox ((x , y) , hu))
...   | inl ¬cv = absurd (not-elim (CritVB x y) ¬cv
                    (and-i (not (vEdgesB x y)) (not (hEdgesB x y and not (black x y)))
                      (not-i (vEdgesB x y) ¬d)
                      (not-i (hEdgesB x y and not (black x y))
                        (λ h → not-elim (black x y)
                                 (and-r (hEdgesB x y) (not (black x y)) h)
                                 (f (and-l (hEdgesB x y) (not (black x y)) h))))))
...   | inr m   = m

--------------------------------------------------------------------------------
-- Every cell of the Morse complex is one of the table's
--
-- `edgeIs` identifies an arbitrary edge with the one at its position, and the
-- table entry says which arrow of the graph that is; `vF` does the same for
-- vertices.  The two `refl`s at every call site are the computations that tie
-- the table to the picture.

EFact : ℕ → ℕ → Type
EFact x y = {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d) → pos (src (fst f Mo.ₑ)) ≡ (x , y)
          → Σ[ a ∈ Arr (F c) (F d) ] (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))

eF : (x y : ℕ)
     {hu : Bool→Type (vertexB x y)} {hv : Bool→Type (vertexB (suc x) y)}
     {he : Bool→Type (hEdgesB x y)} {nb : Bool→Type (not (black x y))}
     {vd : Bool→Type (vEdgesB x y)} {hd : Bool→Type (vertexB x (suc y))}
     (a₀ : Arr (F (srcSink x y {hu})) (F (tgtSink x y {hv})))
   → arrow (srcSink x y {hu}) (tgtSink x y {hv}) (arrAt x y {hu} {hv} {he} {nb} {vd} {hd})
       ≡ arrow (G (F (srcSink x y {hu}))) (G (F (tgtSink x y {hv})))
               (G₁ (F (srcSink x y {hu})) (F (tgtSink x y {hv})) a₀)
   → EFact x y
eF x y a₀ e {c} {d} f h =
  subst2 (λ i j → Σ[ a ∈ Arr i j ] (arrow c d f ≡ arrow (G i) (G j) (G₁ i j a)))
    (sym (cong F (cong fst β))) (sym (cong F (cong (λ z → fst (snd z)) β)))
    (a₀ , β ∙ e)
  where β = edgeIs x y f h

eFacts : AllPos {P = EFact} eList
eFacts =
      eF 23 10 a0 refl
    ∷ eF 19 11 a1 refl
    ∷ eF 47 11 a2 refl
    ∷ eF 46 12 a3 refl
    ∷ eF 17 13 a4 refl
    ∷ eF 43 13 a5 refl
    ∷ eF 16 14 a6 refl
    ∷ eF 15 15 a7 refl
    ∷ eF 34 15 a8 refl
    ∷ eF 14 16 a9 refl
    ∷ eF 31 16 a10 refl
    ∷ eF 39 16 a11 refl
    ∷ eF 42 16 a12 refl
    ∷ eF 13 17 a13 refl
    ∷ eF 30 17 a14 refl
    ∷ eF 38 17 a15 refl
    ∷ eF 12 18 a16 refl
    ∷ eF 27 18 a17 refl
    ∷ eF 37 18 a18 refl
    ∷ eF 11 19 a19 refl
    ∷ eF 35 19 a20 refl
    ∷ eF 34 20 a21 refl
    ∷ eF 10 21 a22 refl
    ∷ eF 9 26 a23 refl
    ∷ eF 8 27 a24 refl
    ∷ eF 2 29 a25 refl
    ∷ eF 61 29 a26 refl
    ∷ eF 45 32 a27 refl
    ∷ eF 59 32 a28 refl
    ∷ eF 18 35 a29 refl
    ∷ eF 28 36 a30 refl
    ∷ eF 39 36 a31 refl
    ∷ eF 43 36 a32 refl
    ∷ eF 58 36 a33 refl
    ∷ eF 37 37 a34 refl
    ∷ eF 57 37 a35 refl
    ∷ eF 56 39 a36 refl
    ∷ eF 55 40 a37 refl
    ∷ eF 26 44 a38 refl
    ∷ eF 37 44 a39 refl
    ∷ eF 25 45 a40 refl
    ∷ eF 23 46 a41 refl
    ∷ eF 54 46 a42 refl
    ∷ eF 22 47 a43 refl
    ∷ eF 41 47 a44 refl
    ∷ eF 53 48 a45 refl
    ∷ eF 43 49 a46 refl
    ∷ eF 51 50 a47 refl
    ∷ eF 42 52 a48 refl
    ∷ eF 50 52 a49 refl
    ∷ eF 41 53 a50 refl
    ∷ eF 32 54 a51 refl
    ∷ eF 49 55 a52 refl
    ∷ eF 46 56 a53 refl
    ∷ eF 44 58 a54 refl
    ∷ eF 43 59 a55 refl
    ∷ eF 41 60 a56 refl
    ∷ eF 39 61 a57 refl
    ∷ eF 38 62 a58 refl
  ∷ []

eFact : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
  → Σ[ a ∈ Arr (F c) (F d) ] (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))
eFact c d f = allFrom eFacts (fst (pos (src (fst f Mo.ₑ))))
                             (snd (pos (src (fst f Mo.ₑ)))) (eMem {c} {d} f)
                      {c} {d} f (λ _ → pos (src (fst f Mo.ₑ)))

F₁ : (c d : Mo.Crit₀) → Mo⁻.Crit₁ c d → Arr (F c) (F d)
F₁ c d f = fst (eFact c d f)

F₁id : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
  → arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) (F₁ c d f))
F₁id c d f = snd (eFact c d f)

VFact : ℕ → ℕ → Type
VFact x y = (c : Mo.Crit₀) → pos (c Mo.ᵥ) ≡ (x , y) → G (F c) ≡ c

vF : (x y : ℕ) {h : Bool→Type (vertexB x y)} (w : Vtx)
   → pos (CritAt x y {h} Mo.ᵥ) ≡ (x , y)     -- the position is Critical: it is its own sink
   → F (CritAt x y {h}) ≡ w                  -- the table finds it …
   → G w ≡ CritAt x y {h}                    -- … and finds it again
   → VFact x y
vF x y {h} w e₀ e₁ e₂ c hp =
  cong (λ z → G (F z)) γ ∙ cong G e₁ ∙ e₂ ∙ sym γ
  where γ : c ≡ CritAt x y {h}
        γ = CritEq (hp ∙ sym e₀)

vFacts : AllPos {P = VFact} vList
vFacts =
      vF 23 11 v0 refl refl refl
    ∷ vF 47 12 v1 refl refl refl
    ∷ vF 19 13 v2 refl refl refl
    ∷ vF 46 13 v3 refl refl refl
    ∷ vF 17 14 v4 refl refl refl
    ∷ vF 16 15 v5 refl refl refl
    ∷ vF 15 16 v6 refl refl refl
    ∷ vF 34 16 v7 refl refl refl
    ∷ vF 43 16 v8 refl refl refl
    ∷ vF 14 17 v9 refl refl refl
    ∷ vF 31 17 v10 refl refl refl
    ∷ vF 39 17 v11 refl refl refl
    ∷ vF 13 18 v12 refl refl refl
    ∷ vF 30 18 v13 refl refl refl
    ∷ vF 38 18 v14 refl refl refl
    ∷ vF 42 18 v15 refl refl refl
    ∷ vF 12 19 v16 refl refl refl
    ∷ vF 27 19 v17 refl refl refl
    ∷ vF 37 19 v18 refl refl refl
    ∷ vF 35 20 v19 refl refl refl
    ∷ vF 11 21 v20 refl refl refl
    ∷ vF 34 22 v21 refl refl refl
    ∷ vF 10 26 v22 refl refl refl
    ∷ vF 9 27 v23 refl refl refl
    ∷ vF 63 29 v24 refl refl refl
    ∷ vF 2 31 v25 refl refl refl
    ∷ vF 48 32 v26 refl refl refl
    ∷ vF 61 32 v27 refl refl refl
    ∷ vF 8 33 v28 refl refl refl
    ∷ vF 18 36 v29 refl refl refl
    ∷ vF 30 36 v30 refl refl refl
    ∷ vF 59 36 v31 refl refl refl
    ∷ vF 28 37 v32 refl refl refl
    ∷ vF 39 37 v33 refl refl refl
    ∷ vF 43 37 v34 refl refl refl
    ∷ vF 58 37 v35 refl refl refl
    ∷ vF 57 39 v36 refl refl refl
    ∷ vF 56 40 v37 refl refl refl
    ∷ vF 27 44 v38 refl refl refl
    ∷ vF 26 45 v39 refl refl refl
    ∷ vF 37 45 v40 refl refl refl
    ∷ vF 25 46 v41 refl refl refl
    ∷ vF 55 46 v42 refl refl refl
    ∷ vF 23 47 v43 refl refl refl
    ∷ vF 42 47 v44 refl refl refl
    ∷ vF 54 48 v45 refl refl refl
    ∷ vF 47 49 v46 refl refl refl
    ∷ vF 53 50 v47 refl refl refl
    ∷ vF 43 52 v48 refl refl refl
    ∷ vF 51 52 v49 refl refl refl
    ∷ vF 42 53 v50 refl refl refl
    ∷ vF 32 55 v51 refl refl refl
    ∷ vF 41 55 v52 refl refl refl
    ∷ vF 50 55 v53 refl refl refl
    ∷ vF 49 56 v54 refl refl refl
    ∷ vF 46 58 v55 refl refl refl
    ∷ vF 44 59 v56 refl refl refl
    ∷ vF 43 60 v57 refl refl refl
    ∷ vF 41 61 v58 refl refl refl
    ∷ vF 39 62 v59 refl refl refl
    ∷ vF 38 63 v60 refl refl refl
  ∷ []

R : (c : Mo.Crit₀) → G (F c) ≡ c
R c = allFrom vFacts (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) (vMem c) c
              (λ _ → pos (c Mo.ᵥ))

--------------------------------------------------------------------------------
-- The two graphs are the same, and hence so are their realisations
--
-- Both round-trips are propositions: an arrow of the graph is determined by
-- its endpoints (no two Critical edges of a forest are parallel), and an edge
-- of the Morse complex is determined by the arrow it maps to.

CritIsSet : isHSet Mo.Crit₀
CritIsSet = Mo.Crit₀IsHSet

arrowFib : {c d : Mo.Crit₀} {f f' : Mo⁻.Crit₁ c d} → arrow c d f ≡ arrow c d f' → f ≡ f'
arrowFib {c} {d} {f} {f'} β =
  subst2 (λ a b → PathP (λ i → Mo⁻.Crit₁ (a i) (b i)) f f')
    (CritIsSet c c (λ i → fst (β i)) refl)
    (CritIsSet d d (λ i → fst (snd (β i))) refl)
    (λ i → snd (snd (β i)))

isPropCrit₁ᴹ : {c d : Mo.Crit₀} → isHProp (Mo⁻.Crit₁ c d)
isPropCrit₁ᴹ {c} {d} f f' = arrowFib
  (F₁id c d f
    ∙ cong (λ a → arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))
        (isPropArr (F c) (F d) (F₁ c d f) (F₁ c d f'))
    ∙ sym (F₁id c d f'))

S₁ : (i j : Vtx) (a : Arr i j)
   → PathP (λ k → Arr (S i k) (S j k)) (F₁ (G i) (G j) (G₁ i j a)) a
S₁ i j a = toPathP (isPropArr i j (transport (λ k → Arr (S i k) (S j k))
                                     (F₁ (G i) (G j) (G₁ i j a))) a)

R₁ : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
   → PathP (λ k → Mo⁻.Crit₁ (R c k) (R d k)) (G₁ (F c) (F d) (F₁ c d f)) f
R₁ c d f = toPathP (isPropCrit₁ᴹ {c} {d}
  (transport (λ k → Mo⁻.Crit₁ (R c k) (R d k)) (G₁ (F c) (F d) (F₁ c d f))) f)

Crit₁ᴹ≡Arr : GR.∣ Mo.Crit₀ , Mo⁻.Crit₁ ∣ ≡ GR.∣ Vtx , Arr ∣
Crit₁ᴹ≡Arr = GR.isoReal F F₁ G G₁ S S₁ R R₁

--------------------------------------------------------------------------------
-- The theorem

∣voevodsky∣≡Bool : ∣ V , E , Sq ∣ ≡ Bool
∣voevodsky∣≡Bool = Mo.MorseTheorem ∙ Crit₁ᴹ≡Arr ∙ ∣Arr∣≡Bool

