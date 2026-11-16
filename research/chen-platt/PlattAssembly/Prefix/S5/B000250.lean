import PlattAssemblyKernel
import PlattCertificates.Count131072.C048000
import PlattCertificates.Count131072.C048001
import PlattCertificates.Count131072.C048002
import PlattCertificates.Count131072.C048003
import PlattCertificates.Count131072.C048004
import PlattCertificates.Count131072.C048005
import PlattCertificates.Count131072.C048006
import PlattCertificates.Count131072.C048007
import PlattCertificates.Count131072.C048008
import PlattCertificates.Count131072.C048009
import PlattCertificates.Count131072.C048010
import PlattCertificates.Count131072.C048011
import PlattCertificates.Count131072.C048012
import PlattCertificates.Count131072.C048013
import PlattCertificates.Count131072.C048014
import PlattCertificates.Count131072.C048015
import PlattCertificates.Count131072.C048016
import PlattCertificates.Count131072.C048017
import PlattCertificates.Count131072.C048018
import PlattCertificates.Count131072.C048019
import PlattCertificates.Count131072.C048020
import PlattCertificates.Count131072.C048021
import PlattCertificates.Count131072.C048022
import PlattCertificates.Count131072.C048023
import PlattCertificates.Count131072.C048024
import PlattCertificates.Count131072.C048025
import PlattCertificates.Count131072.C048026
import PlattCertificates.Count131072.C048027
import PlattCertificates.Count131072.C048028
import PlattCertificates.Count131072.C048029
import PlattCertificates.Count131072.C048030
import PlattCertificates.Count131072.C048031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48000 : List PrefixCut := [⟨3,11446083,11446090⟩,
⟨64,259143922,259144064⟩]
theorem checked48000 : checkPrefixCuts (2^48) 6295388161 10 Manual.Count131072.C048000.packed 64 cuts48000 = true := by
 decide +kernel
def pointBounds48000 : List (Nat × Nat × Nat) := [(6295394304,111148434156062,111148820987951)]
theorem point_links_checked48000 : (cuts48000.take 1).map (fun c => (6295388161-1+2*2^10*c.k,111148422709979+c.lower,111148809541861+c.upper)) = pointBounds48000 := by
 decide +kernel
def cuts48001 : List PrefixCut := [⟨36,150270625,150270709⟩,
⟨64,262894181,262894328⟩]
theorem checked48001 : checkPrefixCuts (2^48) 6295519233 10 Manual.Count131072.C048001.packed 64 cuts48001 = true := by
 decide +kernel
def pointBounds48001 : List (Nat × Nat × Nat) := [(6295592960,111148832124526,111149218956634)]
theorem point_links_checked48001 : (cuts48001.take 1).map (fun c => (6295519233-1+2*2^10*c.k,111148681853901+c.lower,111149068685925+c.upper)) = pointBounds48001 := by
 decide +kernel
def cuts48002 : List PrefixCut := [⟨64,265437086,265437229⟩]
theorem checked48002 : checkPrefixCuts (2^48) 6295650305 10 Manual.Count131072.C048002.packed 64 cuts48002 = true := by
 decide +kernel
def cuts48003 : List PrefixCut := [⟨5,19582304,19582316⟩,
⟨64,256579370,256579516⟩]
theorem checked48003 : checkPrefixCuts (2^48) 6295781377 10 Manual.Count131072.C048003.packed 64 cuts48003 = true := by
 decide +kernel
def pointBounds48003 : List (Nat × Nat × Nat) := [(6295791616,111149229767472,111149616599798)]
theorem point_links_checked48003 : (cuts48003.take 1).map (fun c => (6295781377-1+2*2^10*c.k,111149210185168+c.lower,111149597017482+c.upper)) = pointBounds48003 := by
 decide +kernel
def cuts48004 : List PrefixCut := [⟨38,152228306,152228390⟩,
⟨64,261089411,261089559⟩]
theorem checked48004 : checkPrefixCuts (2^48) 6295912449 10 Manual.Count131072.C048004.packed 64 cuts48004 = true := by
 decide +kernel
def pointBounds48004 : List (Nat × Nat × Nat) := [(6295990272,111149618992844,111150005825388)]
theorem point_links_checked48004 : (cuts48004.take 1).map (fun c => (6295912449-1+2*2^10*c.k,111149466764538+c.lower,111149853596998+c.upper)) = pointBounds48004 := by
 decide +kernel
def cuts48005 : List PrefixCut := [⟨64,259698134,259698282⟩]
theorem checked48005 : checkPrefixCuts (2^48) 6296043521 10 Manual.Count131072.C048005.packed 64 cuts48005 = true := by
 decide +kernel
def cuts48006 : List PrefixCut := [⟨7,28969263,28969278⟩,
⟨64,259826863,259827008⟩]
theorem checked48006 : checkPrefixCuts (2^48) 6296174593 10 Manual.Count131072.C048006.packed 64 cuts48006 = true := by
 decide +kernel
def pointBounds48006 : List (Nat × Nat × Nat) := [(6296188928,111150016521346,111150403354117)]
theorem point_links_checked48006 : (cuts48006.take 1).map (fun c => (6296174593-1+2*2^10*c.k,111149987552083+c.lower,111150374384839+c.upper)) = pointBounds48006 := by
 decide +kernel
def cuts48007 : List PrefixCut := [⟨40,163707811,163707907⟩,
⟨64,264381250,264381406⟩]
theorem checked48007 : checkPrefixCuts (2^48) 6296305665 10 Manual.Count131072.C048007.packed 64 cuts48007 = true := by
 decide +kernel
def pointBounds48007 : List (Nat × Nat × Nat) := [(6296387584,111150411086757,111150797919754)]
theorem point_links_checked48007 : (cuts48007.take 1).map (fun c => (6296305665-1+2*2^10*c.k,111150247378946+c.lower,111150634211847+c.upper)) = pointBounds48007 := by
 decide +kernel
def cuts48008 : List PrefixCut := [⟨64,253870452,253870601⟩]
theorem checked48008 : checkPrefixCuts (2^48) 6296436737 10 Manual.Count131072.C048008.packed 64 cuts48008 = true := by
 decide +kernel
def cuts48009 : List PrefixCut := [⟨9,34599998,34600021⟩,
⟨64,256368482,256368631⟩]
theorem checked48009 : checkPrefixCuts (2^48) 6296567809 10 Manual.Count131072.C048009.packed 64 cuts48009 = true := by
 decide +kernel
def pointBounds48009 : List (Nat × Nat × Nat) := [(6296586240,111150800230646,111151187063875)]
theorem point_links_checked48009 : (cuts48009.take 1).map (fun c => (6296567809-1+2*2^10*c.k,111150765630648+c.lower,111151152463854+c.upper)) = pointBounds48009 := by
 decide +kernel
def cuts48010 : List PrefixCut := [⟨42,171296787,171296887⟩,
⟨64,258777056,258777205⟩]
theorem checked48010 : checkPrefixCuts (2^48) 6296698881 10 Manual.Count131072.C048010.packed 64 cuts48010 = true := by
 decide +kernel
def pointBounds48010 : List (Nat × Nat × Nat) := [(6296784896,111151193295917,111151580129372)]
theorem point_links_checked48010 : (cuts48010.take 1).map (fun c => (6296698881-1+2*2^10*c.k,111151021999130+c.lower,111151408832485+c.upper)) = pointBounds48010 := by
 decide +kernel
def cuts48011 : List PrefixCut := [⟨64,259486882,259487029⟩]
theorem checked48011 : checkPrefixCuts (2^48) 6296829953 10 Manual.Count131072.C048011.packed 64 cuts48011 = true := by
 decide +kernel
def cuts48012 : List PrefixCut := [⟨11,44565939,44565963⟩,
⟨64,259257995,259258149⟩]
theorem checked48012 : checkPrefixCuts (2^48) 6296961025 10 Manual.Count131072.C048012.packed 64 cuts48012 = true := by
 decide +kernel
def pointBounds48012 : List (Nat × Nat × Nat) := [(6296983552,111151584829007,111151971662682)]
theorem point_links_checked48012 : (cuts48012.take 1).map (fun c => (6296961025-1+2*2^10*c.k,111151540263068+c.lower,111151927096719+c.upper)) = pointBounds48012 := by
 decide +kernel
def cuts48013 : List PrefixCut := [⟨44,182684268,182684369⟩,
⟨64,264392946,264393096⟩]
theorem checked48013 : checkPrefixCuts (2^48) 6297092097 10 Manual.Count131072.C048013.packed 64 cuts48013 = true := by
 decide +kernel
def pointBounds48013 : List (Nat × Nat × Nat) := [(6297182208,111151982205331,111152369039237)]
theorem point_links_checked48013 : (cuts48013.take 1).map (fun c => (6297092097-1+2*2^10*c.k,111151799521063+c.lower,111152186354868+c.upper)) = pointBounds48013 := by
 decide +kernel
def cuts48014 : List PrefixCut := [⟨64,257772161,257772314⟩]
theorem checked48014 : checkPrefixCuts (2^48) 6297223169 10 Manual.Count131072.C048014.packed 64 cuts48014 = true := by
 decide +kernel
def cuts48015 : List PrefixCut := [⟨13,54128348,54128379⟩,
⟨64,263219811,263219964⟩]
theorem checked48015 : checkPrefixCuts (2^48) 6297354241 10 Manual.Count131072.C048015.packed 64 cuts48015 = true := by
 decide +kernel
def pointBounds48015 : List (Nat × Nat × Nat) := [(6297380864,111152375814518,111152762648657)]
theorem point_links_checked48015 : (cuts48015.take 1).map (fun c => (6297354241-1+2*2^10*c.k,111152321686170+c.lower,111152708520278+c.upper)) = pointBounds48015 := by
 decide +kernel
def cuts48016 : List PrefixCut := [⟨46,184103080,184103187⟩,
⟨64,257180381,257180529⟩]
theorem checked48016 : checkPrefixCuts (2^48) 6297485313 10 Manual.Count131072.C048016.packed 64 cuts48016 = true := by
 decide +kernel
def pointBounds48016 : List (Nat × Nat × Nat) := [(6297579520,111152769009061,111153155843429)]
theorem point_links_checked48016 : (cuts48016.take 1).map (fun c => (6297485313-1+2*2^10*c.k,111152584905981+c.lower,111152971740242+c.upper)) = pointBounds48016 := by
 decide +kernel
def cuts48017 : List PrefixCut := [⟨64,259275696,259275837⟩]
theorem checked48017 : checkPrefixCuts (2^48) 6297616385 10 Manual.Count131072.C048017.packed 64 cuts48017 = true := by
 decide +kernel
def cuts48018 : List PrefixCut := [⟨15,61231365,61231400⟩,
⟨64,261236864,261237011⟩]
theorem checked48018 : checkPrefixCuts (2^48) 6297747457 10 Manual.Count131072.C048018.packed 64 cuts48018 = true := by
 decide +kernel
def pointBounds48018 : List (Nat × Nat × Nat) := [(6297778176,111153162593423,111153549428008)]
theorem point_links_checked48018 : (cuts48018.take 1).map (fun c => (6297747457-1+2*2^10*c.k,111153101362058+c.lower,111153488196608+c.upper)) = pointBounds48018 := by
 decide +kernel
def cuts48019 : List PrefixCut := [⟨48,197499497,197499613⟩,
⟨64,261678343,261678495⟩]
theorem checked48019 : checkPrefixCuts (2^48) 6297878529 10 Manual.Count131072.C048019.packed 64 cuts48019 = true := by
 decide +kernel
def pointBounds48019 : List (Nat × Nat × Nat) := [(6297976832,111153560098419,111153946933232)]
theorem point_links_checked48019 : (cuts48019.take 1).map (fun c => (6297878529-1+2*2^10*c.k,111153362598922+c.lower,111153749433619+c.upper)) = pointBounds48019 := by
 decide +kernel
def cuts48020 : List PrefixCut := [⟨64,259795814,259795958⟩]
theorem checked48020 : checkPrefixCuts (2^48) 6298009601 10 Manual.Count131072.C048020.packed 64 cuts48020 = true := by
 decide +kernel
def cuts48021 : List PrefixCut := [⟨17,70165850,70165889⟩,
⟨64,259388211,259388355⟩]
theorem checked48021 : checkPrefixCuts (2^48) 6298140673 10 Manual.Count131072.C048021.packed 64 cuts48021 = true := by
 decide +kernel
def pointBounds48021 : List (Nat × Nat × Nat) := [(6298175488,111153954238929,111154341073961)]
theorem point_links_checked48021 : (cuts48021.take 1).map (fun c => (6298140673-1+2*2^10*c.k,111153884073079+c.lower,111154270908072+c.upper)) = pointBounds48021 := by
 decide +kernel
def cuts48022 : List PrefixCut := [⟨50,202090231,202090343⟩,
⟨64,258399615,258399760⟩]
theorem checked48022 : checkPrefixCuts (2^48) 6298271745 10 Manual.Count131072.C048022.packed 64 cuts48022 = true := by
 decide +kernel
def pointBounds48022 : List (Nat × Nat × Nat) := [(6298374144,111154345551521,111154732386770)]
theorem point_links_checked48022 : (cuts48022.take 1).map (fun c => (6298271745-1+2*2^10*c.k,111154143461290+c.lower,111154530296427+c.upper)) = pointBounds48022 := by
 decide +kernel
def cuts48023 : List PrefixCut := [⟨64,259332695,259332840⟩]
theorem checked48023 : checkPrefixCuts (2^48) 6298402817 10 Manual.Count131072.C048023.packed 64 cuts48023 = true := by
 decide +kernel
def cuts48024 : List PrefixCut := [⟨19,76194432,76194480⟩,
⟨64,257092889,257093038⟩]
theorem checked48024 : checkPrefixCuts (2^48) 6298533889 10 Manual.Count131072.C048024.packed 64 cuts48024 = true := by
 decide +kernel
def pointBounds48024 : List (Nat × Nat × Nat) := [(6298572800,111154737388032,111155124223507)]
theorem point_links_checked48024 : (cuts48024.take 1).map (fun c => (6298533889-1+2*2^10*c.k,111154661193600+c.lower,111155048029027+c.upper)) = pointBounds48024 := by
 decide +kernel
def cuts48025 : List PrefixCut := [⟨52,213651656,213651776⟩,
⟨64,263209742,263209888⟩]
theorem checked48025 : checkPrefixCuts (2^48) 6298664961 10 Manual.Count131072.C048025.packed 64 cuts48025 = true := by
 decide +kernel
def pointBounds48025 : List (Nat × Nat × Nat) := [(6298771456,111155131938145,111155518773841)]
theorem point_links_checked48025 : (cuts48025.take 1).map (fun c => (6298664961-1+2*2^10*c.k,111154918286489+c.lower,111155305122065+c.upper)) = pointBounds48025 := by
 decide +kernel
def cuts48026 : List PrefixCut := [⟨64,265304514,265304655⟩]
theorem checked48026 : checkPrefixCuts (2^48) 6298796033 10 Manual.Count131072.C048026.packed 64 cuts48026 = true := by
 decide +kernel
def cuts48027 : List PrefixCut := [⟨21,86065263,86065312⟩,
⟨64,259713298,259713453⟩]
theorem checked48027 : checkPrefixCuts (2^48) 6298927105 10 Manual.Count131072.C048027.packed 64 cuts48027 = true := by
 decide +kernel
def pointBounds48027 : List (Nat × Nat × Nat) := [(6298970112,111155532866008,111155919701920)]
theorem point_links_checked48027 : (cuts48027.take 1).map (fun c => (6298927105-1+2*2^10*c.k,111155446800745+c.lower,111155833636608+c.upper)) = pointBounds48027 := by
 decide +kernel
def cuts48028 : List PrefixCut := [⟨54,221234649,221234777⟩,
⟨64,262925176,262925326⟩]
theorem checked48028 : checkPrefixCuts (2^48) 6299058177 10 Manual.Count131072.C048028.packed 64 cuts48028 = true := by
 decide +kernel
def pointBounds48028 : List (Nat × Nat × Nat) := [(6299168768,111155927748692,111156314584838)]
theorem point_links_checked48028 : (cuts48028.take 1).map (fun c => (6299058177-1+2*2^10*c.k,111155706514043+c.lower,111156093350061+c.upper)) = pointBounds48028 := by
 decide +kernel
def cuts48029 : List PrefixCut := [⟨64,263902776,263902926⟩]
theorem checked48029 : checkPrefixCuts (2^48) 6299189249 10 Manual.Count131072.C048029.packed 64 cuts48029 = true := by
 decide +kernel
def cuts48030 : List PrefixCut := [⟨23,91109062,91109121⟩,
⟨64,254871311,254871462⟩]
theorem checked48030 : checkPrefixCuts (2^48) 6299320321 10 Manual.Count131072.C048030.packed 64 cuts48030 = true := by
 decide +kernel
def pointBounds48030 : List (Nat × Nat × Nat) := [(6299367424,111156324451057,111156711287434)]
theorem point_links_checked48030 : (cuts48030.take 1).map (fun c => (6299320321-1+2*2^10*c.k,111156233341995+c.lower,111156620178313+c.upper)) = pointBounds48030 := by
 decide +kernel
def cuts48031 : List PrefixCut := [⟨56,221310148,221310276⟩,
⟨64,254106423,254106570⟩]
theorem checked48031 : checkPrefixCuts (2^48) 6299451393 10 Manual.Count131072.C048031.packed 64 cuts48031 = true := by
 decide +kernel
def pointBounds48031 : List (Nat × Nat × Nat) := [(6299566080,111156709523454,111157096360051)]
theorem point_links_checked48031 : (cuts48031.take 1).map (fun c => (6299451393-1+2*2^10*c.k,111156488213306+c.lower,111156875049775+c.upper)) = pointBounds48031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000250
