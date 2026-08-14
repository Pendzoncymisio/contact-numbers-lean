import ContactNumbers.Emin9
import ContactNumbers.Cap9
import ContactNumbers.Emin9TreeC0
import ContactNumbers.Emin9TreeC1
import ContactNumbers.Emin9TreeC2
import ContactNumbers.Emin9TreeC3
import ContactNumbers.Emin9TreeC4
import ContactNumbers.Emin9TreeC5

set_option linter.style.header false
set_option maxRecDepth 1000000

/-! # E_min(9): the assembled kill tree and the ground-state bound

The 131325-node canonical-enumeration tree is checked in chunks by the
kernel and recomposed here with `walk_branch` / `walk_fuel_mono`.  Every
leaf carries a certificate discharged by one of the 23 kill kinds, so no
hard-core nine-point configuration reaches 43 ordered contacts. -/

namespace Kissing3D
namespace Emin9T

lemma nine_tree : walk 8022 (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg0 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg1 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg2 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg3 ++ ((0 : ℕ) :: (sg4 ++ sg5)))) ++ sg6)))) ++ ((0 : ℕ) :: (sg7 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg8 ++ ((0 : ℕ) :: (sg9 ++ sg10)))) ++ sg11)))))))) ++ sg12)) ++ sg13)))) ++ ((0 : ℕ) :: (sg14 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg15 ++ ((0 : ℕ) :: (sg16 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg17 ++ ((0 : ℕ) :: (sg18 ++ sg19)))) ++ sg20)) ++ sg21)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg22 ++ ((0 : ℕ) :: (sg23 ++ sg24)))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg25 ++ ((0 : ℕ) :: (sg26 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg27 ++ sg28)) ++ sg29)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg30 ++ sg31)) ++ sg32)))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg33 ++ ((0 : ℕ) :: (sg34 ++ ((0 : ℕ) :: (sg35 ++ sg36)))))) ++ ((0 : ℕ) :: (sg37 ++ sg38)))))))) ++ ((0 : ℕ) :: (sg39 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg40 ++ ((0 : ℕ) :: (sg41 ++ sg42)))) ++ sg43)))))))) ++ sg44)))))) ++ ((0 : ℕ) :: (sg45 ++ ((0 : ℕ) :: (sg46 ++ ((0 : ℕ) :: (sg47 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg48 ++ ((0 : ℕ) :: (sg49 ++ sg50)))) ++ sg51)) ++ sg52)))))))))) ++ sg53)) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg54 ++ ((0 : ℕ) :: (sg55 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg56 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg57 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg58 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg59 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg60 ++ sg61)) ++ sg62)))) ++ sg63)))) ++ ((0 : ℕ) :: (sg64 ++ sg65)))))) ++ ((0 : ℕ) :: (sg66 ++ ((0 : ℕ) :: (sg67 ++ sg68)))))) ++ sg69)))) ++ sg70)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg71 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg72 ++ ((0 : ℕ) :: (sg73 ++ ((0 : ℕ) :: (sg74 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg75 ++ sg76)) ++ sg77)))))))) ++ sg78)))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg79 ++ ((0 : ℕ) :: (sg80 ++ ((0 : ℕ) :: (sg81 ++ sg82)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg83 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg84 ++ sg85)) ++ sg86)))) ++ ((0 : ℕ) :: (sg87 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg88 ++ sg89)) ++ sg90)))))))) ++ sg91)) ++ sg92)))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg93 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg94 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg95 ++ ((0 : ℕ) :: (sg96 ++ sg97)))) ++ sg98)) ++ ((0 : ℕ) :: (sg99 ++ sg100)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg101 ++ ((0 : ℕ) :: (sg102 ++ ((0 : ℕ) :: (sg103 ++ sg104)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg105 ++ ((0 : ℕ) :: (sg106 ++ sg107)))) ++ sg108)) ++ sg109)))) ++ ((0 : ℕ) :: (sg110 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg111 ++ sg112)) ++ sg113)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg114 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg115 ++ sg116)) ++ sg117)))) ++ sg118)))))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg119 ++ ((0 : ℕ) :: (sg120 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg121 ++ sg122)) ++ sg123)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg124 ++ ((0 : ℕ) :: (sg125 ++ sg126)))) ++ sg127)))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg128 ++ ((0 : ℕ) :: (sg129 ++ sg130)))) ++ sg131)) ++ sg132)))) ++ sg133)))))) ++ ((0 : ℕ) :: (sg134 ++ ((0 : ℕ) :: (sg135 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg136 ++ ((0 : ℕ) :: (sg137 ++ sg138)))) ++ sg139)) ++ sg140)))))))))) ++ sg141)))) ++ ((0 : ℕ) :: (sg142 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg143 ++ ((0 : ℕ) :: (sg144 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg145 ++ ((0 : ℕ) :: (sg146 ++ ((0 : ℕ) :: (sg147 ++ sg148)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg149 ++ ((0 : ℕ) :: (sg150 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg151 ++ sg152)) ++ sg153)))))) ++ sg154)) ++ sg155)) ++ sg156)))) ++ sg157)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg158 ++ ((0 : ℕ) :: (sg159 ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg160 ++ ((0 : ℕ) :: (sg161 ++ sg162)))) ++ sg163)))))) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg164 ++ ((0 : ℕ) :: (sg165 ++ sg166)))) ++ sg167)))) ++ sg168)))))))) ++ sg169)) ++ ((0 : ℕ) :: (((0 : ℕ) :: (sg170 ++ ((0 : ℕ) :: (sg171 ++ ((0 : ℕ) :: (sg172 ++ ((0 : ℕ) :: (((0 : ℕ) :: (((0 : ℕ) :: (sg173 ++ sg174)) ++ sg175)) ++ sg176)))))))) ++ sg177)))) ++ sg178)) ++ sg179))) 0 [] [] = some [] := by
  have n0 := walk_branch (by norm_num : 17 < 36) ck4 ck5
  have n1 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck3) n0
  have n2 := walk_branch (by norm_num : 15 < 36) n1 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck6)
  have n3 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck2) n2
  have n4 := walk_branch (by norm_num : 17 < 36) ck9 ck10
  have n5 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck8) n4
  have n6 := walk_branch (by norm_num : 15 < 36) n5 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck11)
  have n7 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck7) n6
  have n8 := walk_branch (by norm_num : 13 < 36) n3 n7
  have n9 := walk_branch (by norm_num : 12 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck1) n8
  have n10 := walk_branch (by norm_num : 11 < 36) n9 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck12)
  have n11 := walk_branch (by norm_num : 10 < 36) n10 (walk_fuel_mono (by norm_num : 8001 ≤ 8008) ck13)
  have n12 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8009) ck0) n11
  have n13 := walk_branch (by norm_num : 17 < 36) ck18 ck19
  have n14 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck17) n13
  have n15 := walk_branch (by norm_num : 15 < 36) n14 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck20)
  have n16 := walk_branch (by norm_num : 14 < 36) n15 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck21)
  have n17 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck16) n16
  have n18 := walk_branch (by norm_num : 12 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck15) n17
  have n19 := walk_branch (by norm_num : 15 < 36) ck23 ck24
  have n20 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck22) n19
  have n21 := walk_branch (by norm_num : 19 < 36) ck27 ck28
  have n22 := walk_branch (by norm_num : 18 < 36) n21 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck29)
  have n23 := walk_branch (by norm_num : 17 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck26) n22
  have n24 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck25) n23
  have n25 := walk_branch (by norm_num : 17 < 36) ck30 ck31
  have n26 := walk_branch (by norm_num : 16 < 36) n25 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck32)
  have n27 := walk_branch (by norm_num : 15 < 36) n24 (walk_fuel_mono (by norm_num : 8003 ≤ 8005) n26)
  have n28 := walk_branch (by norm_num : 18 < 36) ck35 ck36
  have n29 := walk_branch (by norm_num : 17 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck34) n28
  have n30 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck33) n29
  have n31 := walk_branch (by norm_num : 16 < 36) ck37 ck38
  have n32 := walk_branch (by norm_num : 15 < 36) n30 (walk_fuel_mono (by norm_num : 8002 ≤ 8004) n31)
  have n33 := walk_branch (by norm_num : 14 < 36) n27 (walk_fuel_mono (by norm_num : 8005 ≤ 8006) n32)
  have n34 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8003 ≤ 8007) n20) n33
  have n35 := walk_branch (by norm_num : 16 < 36) ck41 ck42
  have n36 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck40) n35
  have n37 := walk_branch (by norm_num : 14 < 36) n36 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck43)
  have n38 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck39) n37
  have n39 := walk_branch (by norm_num : 12 < 36) n34 (walk_fuel_mono (by norm_num : 8005 ≤ 8008) n38)
  have n40 := walk_branch (by norm_num : 11 < 36) (walk_fuel_mono (by norm_num : 8007 ≤ 8009) n18) n39
  have n41 := walk_branch (by norm_num : 10 < 36) n40 (walk_fuel_mono (by norm_num : 8001 ≤ 8010) ck44)
  have n42 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8011) ck14) n41
  have n43 := walk_branch (by norm_num : 8 < 36) (walk_fuel_mono (by norm_num : 8010 ≤ 8012) n12) n42
  have n44 := walk_branch (by norm_num : 14 < 36) ck49 ck50
  have n45 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck48) n44
  have n46 := walk_branch (by norm_num : 12 < 36) n45 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck51)
  have n47 := walk_branch (by norm_num : 11 < 36) n46 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck52)
  have n48 := walk_branch (by norm_num : 10 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck47) n47
  have n49 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck46) n48
  have n50 := walk_branch (by norm_num : 8 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck45) n49
  have n51 := walk_branch (by norm_num : 7 < 36) n43 (walk_fuel_mono (by norm_num : 8008 ≤ 8013) n50)
  have n52 := walk_branch (by norm_num : 6 < 36) n51 (walk_fuel_mono (by norm_num : 8001 ≤ 8014) ck53)
  have n53 := walk_branch (by norm_num : 20 < 36) ck60 ck61
  have n54 := walk_branch (by norm_num : 19 < 36) n53 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck62)
  have n55 := walk_branch (by norm_num : 18 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck59) n54
  have n56 := walk_branch (by norm_num : 17 < 36) n55 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck63)
  have n57 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck58) n56
  have n58 := walk_branch (by norm_num : 16 < 36) ck64 ck65
  have n59 := walk_branch (by norm_num : 15 < 36) n57 (walk_fuel_mono (by norm_num : 8002 ≤ 8006) n58)
  have n60 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck57) n59
  have n61 := walk_branch (by norm_num : 15 < 36) ck67 ck68
  have n62 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck66) n61
  have n63 := walk_branch (by norm_num : 13 < 36) n60 (walk_fuel_mono (by norm_num : 8003 ≤ 8008) n62)
  have n64 := walk_branch (by norm_num : 12 < 36) n63 (walk_fuel_mono (by norm_num : 8001 ≤ 8009) ck69)
  have n65 := walk_branch (by norm_num : 11 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8010) ck56) n64
  have n66 := walk_branch (by norm_num : 10 < 36) n65 (walk_fuel_mono (by norm_num : 8001 ≤ 8011) ck70)
  have n67 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8012) ck55) n66
  have n68 := walk_branch (by norm_num : 8 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8013) ck54) n67
  have n69 := walk_branch (by norm_num : 17 < 36) ck75 ck76
  have n70 := walk_branch (by norm_num : 16 < 36) n69 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck77)
  have n71 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck74) n70
  have n72 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck73) n71
  have n73 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck72) n72
  have n74 := walk_branch (by norm_num : 12 < 36) n73 (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck78)
  have n75 := walk_branch (by norm_num : 11 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck71) n74
  have n76 := walk_branch (by norm_num : 16 < 36) ck81 ck82
  have n77 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck80) n76
  have n78 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck79) n77
  have n79 := walk_branch (by norm_num : 17 < 36) ck84 ck85
  have n80 := walk_branch (by norm_num : 16 < 36) n79 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck86)
  have n81 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck83) n80
  have n82 := walk_branch (by norm_num : 17 < 36) ck88 ck89
  have n83 := walk_branch (by norm_num : 16 < 36) n82 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck90)
  have n84 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck87) n83
  have n85 := walk_branch (by norm_num : 14 < 36) n81 n84
  have n86 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8004 ≤ 8005) n78) n85
  have n87 := walk_branch (by norm_num : 12 < 36) n86 (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck91)
  have n88 := walk_branch (by norm_num : 11 < 36) n87 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck92)
  have n89 := walk_branch (by norm_num : 10 < 36) n75 n88
  have n90 := walk_branch (by norm_num : 17 < 36) ck96 ck97
  have n91 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck95) n90
  have n92 := walk_branch (by norm_num : 15 < 36) n91 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck98)
  have n93 := walk_branch (by norm_num : 15 < 36) ck99 ck100
  have n94 := walk_branch (by norm_num : 14 < 36) n92 (walk_fuel_mono (by norm_num : 8002 ≤ 8004) n93)
  have n95 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck94) n94
  have n96 := walk_branch (by norm_num : 18 < 36) ck103 ck104
  have n97 := walk_branch (by norm_num : 17 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck102) n96
  have n98 := walk_branch (by norm_num : 16 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck101) n97
  have n99 := walk_branch (by norm_num : 19 < 36) ck106 ck107
  have n100 := walk_branch (by norm_num : 18 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck105) n99
  have n101 := walk_branch (by norm_num : 17 < 36) n100 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck108)
  have n102 := walk_branch (by norm_num : 16 < 36) n101 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck109)
  have n103 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8004 ≤ 8005) n98) n102
  have n104 := walk_branch (by norm_num : 17 < 36) ck111 ck112
  have n105 := walk_branch (by norm_num : 16 < 36) n104 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck113)
  have n106 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck110) n105
  have n107 := walk_branch (by norm_num : 14 < 36) n103 (walk_fuel_mono (by norm_num : 8004 ≤ 8006) n106)
  have n108 := walk_branch (by norm_num : 17 < 36) ck115 ck116
  have n109 := walk_branch (by norm_num : 16 < 36) n108 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck117)
  have n110 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck114) n109
  have n111 := walk_branch (by norm_num : 14 < 36) n110 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck118)
  have n112 := walk_branch (by norm_num : 13 < 36) n107 (walk_fuel_mono (by norm_num : 8005 ≤ 8007) n111)
  have n113 := walk_branch (by norm_num : 12 < 36) (walk_fuel_mono (by norm_num : 8006 ≤ 8008) n95) n112
  have n114 := walk_branch (by norm_num : 11 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8009) ck93) n113
  have n115 := walk_branch (by norm_num : 17 < 36) ck121 ck122
  have n116 := walk_branch (by norm_num : 16 < 36) n115 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck123)
  have n117 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck120) n116
  have n118 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck119) n117
  have n119 := walk_branch (by norm_num : 16 < 36) ck125 ck126
  have n120 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck124) n119
  have n121 := walk_branch (by norm_num : 14 < 36) n120 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck127)
  have n122 := walk_branch (by norm_num : 13 < 36) n118 (walk_fuel_mono (by norm_num : 8004 ≤ 8005) n121)
  have n123 := walk_branch (by norm_num : 16 < 36) ck129 ck130
  have n124 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck128) n123
  have n125 := walk_branch (by norm_num : 14 < 36) n124 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck131)
  have n126 := walk_branch (by norm_num : 13 < 36) n125 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck132)
  have n127 := walk_branch (by norm_num : 12 < 36) n122 (walk_fuel_mono (by norm_num : 8005 ≤ 8006) n126)
  have n128 := walk_branch (by norm_num : 11 < 36) n127 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck133)
  have n129 := walk_branch (by norm_num : 10 < 36) n114 (walk_fuel_mono (by norm_num : 8008 ≤ 8010) n128)
  have n130 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8009 ≤ 8011) n89) n129
  have n131 := walk_branch (by norm_num : 14 < 36) ck137 ck138
  have n132 := walk_branch (by norm_num : 13 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck136) n131
  have n133 := walk_branch (by norm_num : 12 < 36) n132 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck139)
  have n134 := walk_branch (by norm_num : 11 < 36) n133 (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck140)
  have n135 := walk_branch (by norm_num : 10 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck135) n134
  have n136 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck134) n135
  have n137 := walk_branch (by norm_num : 8 < 36) n130 (walk_fuel_mono (by norm_num : 8007 ≤ 8012) n136)
  have n138 := walk_branch (by norm_num : 7 < 36) n68 (walk_fuel_mono (by norm_num : 8013 ≤ 8014) n137)
  have n139 := walk_branch (by norm_num : 6 < 36) n138 (walk_fuel_mono (by norm_num : 8001 ≤ 8015) ck141)
  have n140 := walk_branch (by norm_num : 5 < 36) (walk_fuel_mono (by norm_num : 8015 ≤ 8016) n52) n139
  have n141 := walk_branch (by norm_num : 13 < 36) ck147 ck148
  have n142 := walk_branch (by norm_num : 12 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck146) n141
  have n143 := walk_branch (by norm_num : 11 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck145) n142
  have n144 := walk_branch (by norm_num : 17 < 36) ck151 ck152
  have n145 := walk_branch (by norm_num : 16 < 36) n144 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck153)
  have n146 := walk_branch (by norm_num : 15 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck150) n145
  have n147 := walk_branch (by norm_num : 14 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck149) n146
  have n148 := walk_branch (by norm_num : 13 < 36) n147 (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck154)
  have n149 := walk_branch (by norm_num : 12 < 36) n148 (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck155)
  have n150 := walk_branch (by norm_num : 11 < 36) n149 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck156)
  have n151 := walk_branch (by norm_num : 10 < 36) (walk_fuel_mono (by norm_num : 8004 ≤ 8008) n143) n150
  have n152 := walk_branch (by norm_num : 9 < 36) n151 (walk_fuel_mono (by norm_num : 8001 ≤ 8009) ck157)
  have n153 := walk_branch (by norm_num : 8 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8010) ck144) n152
  have n154 := walk_branch (by norm_num : 7 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8011) ck143) n153
  have n155 := walk_branch (by norm_num : 13 < 36) ck161 ck162
  have n156 := walk_branch (by norm_num : 12 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck160) n155
  have n157 := walk_branch (by norm_num : 11 < 36) n156 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck163)
  have n158 := walk_branch (by norm_num : 10 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck159) n157
  have n159 := walk_branch (by norm_num : 9 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck158) n158
  have n160 := walk_branch (by norm_num : 11 < 36) ck165 ck166
  have n161 := walk_branch (by norm_num : 10 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck164) n160
  have n162 := walk_branch (by norm_num : 9 < 36) n161 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck167)
  have n163 := walk_branch (by norm_num : 8 < 36) n159 (walk_fuel_mono (by norm_num : 8004 ≤ 8006) n162)
  have n164 := walk_branch (by norm_num : 7 < 36) n163 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck168)
  have n165 := walk_branch (by norm_num : 6 < 36) n154 (walk_fuel_mono (by norm_num : 8008 ≤ 8012) n164)
  have n166 := walk_branch (by norm_num : 5 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8013) ck142) n165
  have n167 := walk_branch (by norm_num : 4 < 36) n140 (walk_fuel_mono (by norm_num : 8014 ≤ 8017) n166)
  have n168 := walk_branch (by norm_num : 3 < 36) n167 (walk_fuel_mono (by norm_num : 8001 ≤ 8018) ck169)
  have n169 := walk_branch (by norm_num : 9 < 36) ck173 ck174
  have n170 := walk_branch (by norm_num : 8 < 36) n169 (walk_fuel_mono (by norm_num : 8001 ≤ 8002) ck175)
  have n171 := walk_branch (by norm_num : 7 < 36) n170 (walk_fuel_mono (by norm_num : 8001 ≤ 8003) ck176)
  have n172 := walk_branch (by norm_num : 6 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8004) ck172) n171
  have n173 := walk_branch (by norm_num : 5 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8005) ck171) n172
  have n174 := walk_branch (by norm_num : 4 < 36) (walk_fuel_mono (by norm_num : 8001 ≤ 8006) ck170) n173
  have n175 := walk_branch (by norm_num : 3 < 36) n174 (walk_fuel_mono (by norm_num : 8001 ≤ 8007) ck177)
  have n176 := walk_branch (by norm_num : 2 < 36) n168 (walk_fuel_mono (by norm_num : 8008 ≤ 8019) n175)
  have n177 := walk_branch (by norm_num : 1 < 36) n176 (walk_fuel_mono (by norm_num : 8001 ≤ 8020) ck178)
  have n178 := walk_branch (by norm_num : 0 < 36) n177 (walk_fuel_mono (by norm_num : 8001 ≤ 8021) ck179)
  exact n178

end Emin9T

open scoped Classical in
/-- **Nine hard-core particles carry at most 42 ordered contacts** (21 bonds). -/
theorem nine_particle_bound {X : Finset E3} (hX : HardCore X)
    (h9 : X.card = 9) : contactCount X ≤ 42 :=
  Emin9T.nine_particle_bound_of_tree Emin9T.nine_tree hX h9

/-- **`E ≥ −21` for nine particles.** -/
theorem energy_ge_nine_particles {X : Finset E3} (hX : HardCore X)
    (h9 : X.card = 9) : -21 ≤ energy X := by
  have hb := nine_particle_bound hX h9
  rw [energy]
  have hc : (contactCount X : ℝ) ≤ 42 := by exact_mod_cast hb
  linarith

/-- The doubly-capped pentagonal bipyramid is exactly optimal. -/
theorem energy_capBipyr9 : energy capBipyr9 = -21 := by
  have h1 := energy_capBipyr9_le
  have h2 := energy_ge_nine_particles hardCore_capBipyr9 card_capBipyr9
  linarith

/-- **`E_min(9) = −21`**: the nine-particle ground-state energy, realised
by the doubly-capped pentagonal bipyramid.  Resolves the case `n = 9` of
the contact-number conjecture `c(n,3) = 3n − 6` (Bezdek–Khan, Conj. 5.2). -/
theorem groundState_nine :
    (∀ X : Finset E3, HardCore X → X.card = 9 → -21 ≤ energy X) ∧
    HardCore capBipyr9 ∧ capBipyr9.card = 9 ∧ energy capBipyr9 = -21 :=
  ⟨fun _ hX h => energy_ge_nine_particles hX h, hardCore_capBipyr9,
    card_capBipyr9, energy_capBipyr9⟩

#print axioms nine_particle_bound
#print axioms energy_ge_nine_particles
#print axioms energy_capBipyr9
#print axioms groundState_nine

end Kissing3D
