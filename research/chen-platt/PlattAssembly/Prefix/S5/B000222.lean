import PlattAssemblyKernel
import PlattCertificates.Count131072.C047104
import PlattCertificates.Count131072.C047105
import PlattCertificates.Count131072.C047106
import PlattCertificates.Count131072.C047107
import PlattCertificates.Count131072.C047108
import PlattCertificates.Count131072.C047109
import PlattCertificates.Count131072.C047110
import PlattCertificates.Count131072.C047111
import PlattCertificates.Count131072.C047112
import PlattCertificates.Count131072.C047113
import PlattCertificates.Count131072.C047114
import PlattCertificates.Count131072.C047115
import PlattCertificates.Count131072.C047116
import PlattCertificates.Count131072.C047117
import PlattCertificates.Count131072.C047118
import PlattCertificates.Count131072.C047119
import PlattCertificates.Count131072.C047120
import PlattCertificates.Count131072.C047121
import PlattCertificates.Count131072.C047122
import PlattCertificates.Count131072.C047123
import PlattCertificates.Count131072.C047124
import PlattCertificates.Count131072.C047125
import PlattCertificates.Count131072.C047126
import PlattCertificates.Count131072.C047127
import PlattCertificates.Count131072.C047128
import PlattCertificates.Count131072.C047129
import PlattCertificates.Count131072.C047130
import PlattCertificates.Count131072.C047131
import PlattCertificates.Count131072.C047132
import PlattCertificates.Count131072.C047133
import PlattCertificates.Count131072.C047134
import PlattCertificates.Count131072.C047135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47104 : List PrefixCut := [⟨64,265254669,265254811⟩]
theorem checked47104 : checkPrefixCuts (2^48) 6177947649 10 Manual.Count131072.C047104.packed 64 cuts47104 = true := by
 decide +kernel
def cuts47105 : List PrefixCut := [⟨6,24420277,24420291⟩,
⟨64,262971053,262971203⟩]
theorem checked47105 : checkPrefixCuts (2^48) 6178078721 10 Manual.Count131072.C047105.packed 64 cuts47105 = true := by
 decide +kernel
def pointBounds47105 : List (Nat × Nat × Nat) := [(6178091008,110913666851711,110914053549185)]
theorem point_links_checked47105 : (cuts47105.take 1).map (fun c => (6178078721-1+2*2^10*c.k,110913642431434+c.lower,110914029128894+c.upper)) = pointBounds47105 := by
 decide +kernel
def cuts47106 : List PrefixCut := [⟨37,156631900,156631991⟩,
⟨64,265699031,265699186⟩]
theorem checked47106 : checkPrefixCuts (2^48) 6178209793 10 Manual.Count131072.C047106.packed 64 cuts47106 = true := by
 decide +kernel
def pointBounds47106 : List (Nat × Nat × Nat) := [(6178285568,110914062034387,110914448732088)]
theorem point_links_checked47106 : (cuts47106.take 1).map (fun c => (6178209793-1+2*2^10*c.k,110913905402487+c.lower,110914292100097+c.upper)) = pointBounds47106 := by
 decide +kernel
def cuts47107 : List PrefixCut := [⟨64,266695651,266695803⟩]
theorem checked47107 : checkPrefixCuts (2^48) 6178340865 10 Manual.Count131072.C047107.packed 64 cuts47107 = true := by
 decide +kernel
def cuts47108 : List PrefixCut := [⟨4,15398379,15398387⟩,
⟨64,263865436,263865581⟩]
theorem checked47108 : checkPrefixCuts (2^48) 6178471937 10 Manual.Count131072.C047108.packed 64 cuts47108 = true := by
 decide +kernel
def pointBounds47108 : List (Nat × Nat × Nat) := [(6178480128,110914453195548,110914839893473)]
theorem point_links_checked47108 : (cuts47108.take 1).map (fun c => (6178471937-1+2*2^10*c.k,110914437797169+c.lower,110914824495086+c.upper)) = pointBounds47108 := by
 decide +kernel
def cuts47109 : List PrefixCut := [⟨35,146781883,146781964⟩,
⟨64,269098800,269098952⟩]
theorem checked47109 : checkPrefixCuts (2^48) 6178603009 10 Manual.Count131072.C047109.packed 64 cuts47109 = true := by
 decide +kernel
def pointBounds47109 : List (Nat × Nat × Nat) := [(6178674688,110914848444488,110915235142631)]
theorem point_links_checked47109 : (cuts47109.take 1).map (fun c => (6178603009-1+2*2^10*c.k,110914701662605+c.lower,110915088360667+c.upper)) = pointBounds47109 := by
 decide +kernel
def cuts47110 : List PrefixCut := [⟨64,264036484,264036640⟩]
theorem checked47110 : checkPrefixCuts (2^48) 6178734081 10 Manual.Count131072.C047110.packed 64 cuts47110 = true := by
 decide +kernel
def cuts47111 : List PrefixCut := [⟨2,8108692,8108696⟩,
⟨64,265670816,265670974⟩]
theorem checked47111 : checkPrefixCuts (2^48) 6178865153 10 Manual.Count131072.C047111.packed 64 cuts47111 = true := by
 decide +kernel
def pointBounds47111 : List (Nat × Nat × Nat) := [(6178869248,110915242906581,110915629604955)]
theorem point_links_checked47111 : (cuts47111.take 1).map (fun c => (6178865153-1+2*2^10*c.k,110915234797889+c.lower,110915621496259+c.upper)) = pointBounds47111 := by
 decide +kernel
def cuts47112 : List PrefixCut := [⟨33,137434159,137434232⟩,
⟨64,266394045,266394189⟩]
theorem checked47112 : checkPrefixCuts (2^48) 6178996225 10 Manual.Count131072.C047112.packed 64 cuts47112 = true := by
 decide +kernel
def pointBounds47112 : List (Nat × Nat × Nat) := [(6179063808,110915637902864,110916024601465)]
theorem point_links_checked47112 : (cuts47112.take 1).map (fun c => (6178996225-1+2*2^10*c.k,110915500468705+c.lower,110915887167233+c.upper)) = pointBounds47112 := by
 decide +kernel
def cuts47113 : List PrefixCut := [⟨64,263928575,263928724⟩]
theorem checked47113 : checkPrefixCuts (2^48) 6179127297 10 Manual.Count131072.C047113.packed 64 cuts47113 = true := by
 decide +kernel
def pointBounds47113 : List (Nat × Nat × Nat) := [(6179258368,110916030791325,110916417490146)]
theorem point_links_checked47113 : (cuts47113.take 1).map (fun c => (6179127297-1+2*2^10*c.k,110915766862750+c.lower,110916153561422+c.upper)) = pointBounds47113 := by
 decide +kernel
def cuts47114 : List PrefixCut := [⟨64,267658181,267658333⟩]
theorem checked47114 : checkPrefixCuts (2^48) 6179258369 10 Manual.Count131072.C047114.packed 64 cuts47114 = true := by
 decide +kernel
def cuts47115 : List PrefixCut := [⟨31,125764558,125764628⟩,
⟨64,264873903,264874056⟩]
theorem checked47115 : checkPrefixCuts (2^48) 6179389441 10 Manual.Count131072.C047115.packed 64 cuts47115 = true := by
 decide +kernel
def pointBounds47115 : List (Nat × Nat × Nat) := [(6179452928,110916424214064,110916810913107)]
theorem point_links_checked47115 : (cuts47115.take 1).map (fun c => (6179389441-1+2*2^10*c.k,110916298449506+c.lower,110916685148479+c.upper)) = pointBounds47115 := by
 decide +kernel
def cuts47116 : List PrefixCut := [⟨62,254528745,254528890⟩,
⟨64,262955251,262955402⟩]
theorem checked47116 : checkPrefixCuts (2^48) 6179520513 10 Manual.Count131072.C047116.packed 64 cuts47116 = true := by
 decide +kernel
def pointBounds47116 : List (Nat × Nat × Nat) := [(6179647488,110916817852154,110917204551425)]
theorem point_links_checked47116 : (cuts47116.take 1).map (fun c => (6179520513-1+2*2^10*c.k,110916563323409+c.lower,110916950022535+c.upper)) = pointBounds47116 := by
 decide +kernel
def cuts47117 : List PrefixCut := [⟨64,267185643,267185800⟩]
theorem checked47117 : checkPrefixCuts (2^48) 6179651585 10 Manual.Count131072.C047117.packed 64 cuts47117 = true := by
 decide +kernel
def cuts47118 : List PrefixCut := [⟨29,122750465,122750539⟩,
⟨64,268683050,268683207⟩]
theorem checked47118 : checkPrefixCuts (2^48) 6179782657 10 Manual.Count131072.C047118.packed 64 cuts47118 = true := by
 decide +kernel
def pointBounds47118 : List (Nat × Nat × Nat) := [(6179842048,110917216214768,110917602914276)]
theorem point_links_checked47118 : (cuts47118.take 1).map (fun c => (6179782657-1+2*2^10*c.k,110917093464303+c.lower,110917480163737+c.upper)) = pointBounds47118 := by
 decide +kernel
def cuts47119 : List PrefixCut := [⟨60,249320362,249320505⟩,
⟨64,264714843,264714994⟩]
theorem checked47119 : checkPrefixCuts (2^48) 6179913729 10 Manual.Count131072.C047119.packed 64 cuts47119 = true := by
 decide +kernel
def pointBounds47119 : List (Nat × Nat × Nat) := [(6180036608,110917611467715,110917998167449)]
theorem point_links_checked47119 : (cuts47119.take 1).map (fun c => (6179913729-1+2*2^10*c.k,110917362147353+c.lower,110917748846944+c.upper)) = pointBounds47119 := by
 decide +kernel
def cuts47120 : List PrefixCut := [⟨64,266485490,266485642⟩]
theorem checked47120 : checkPrefixCuts (2^48) 6180044801 10 Manual.Count131072.C047120.packed 64 cuts47120 = true := by
 decide +kernel
def cuts47121 : List PrefixCut := [⟨27,111811993,111812061⟩,
⟨64,265477841,265477998⟩]
theorem checked47121 : checkPrefixCuts (2^48) 6180175873 10 Manual.Count131072.C047121.packed 64 cuts47121 = true := by
 decide +kernel
def pointBounds47121 : List (Nat × Nat × Nat) := [(6180231168,110918005159679,110918391859641)]
theorem point_links_checked47121 : (cuts47121.take 1).map (fun c => (6180175873-1+2*2^10*c.k,110917893347686+c.lower,110918280047580+c.upper)) = pointBounds47121 := by
 decide +kernel
def cuts47122 : List PrefixCut := [⟨58,237690985,237691118⟩,
⟨64,261100044,261100189⟩]
theorem checked47122 : checkPrefixCuts (2^48) 6180306945 10 Manual.Count131072.C047122.packed 64 cuts47122 = true := by
 decide +kernel
def pointBounds47122 : List (Nat × Nat × Nat) := [(6180425728,110918396516512,110918783216696)]
theorem point_links_checked47122 : (cuts47122.take 1).map (fun c => (6180306945-1+2*2^10*c.k,110918158825527+c.lower,110918545525578+c.upper)) = pointBounds47122 := by
 decide +kernel
def cuts47123 : List PrefixCut := [⟨64,268836714,268836867⟩]
theorem checked47123 : checkPrefixCuts (2^48) 6180438017 10 Manual.Count131072.C047123.packed 64 cuts47123 = true := by
 decide +kernel
def cuts47124 : List PrefixCut := [⟨25,103561866,103561931⟩,
⟨64,266052989,266053152⟩]
theorem checked47124 : checkPrefixCuts (2^48) 6180569089 10 Manual.Count131072.C047124.packed 64 cuts47124 = true := by
 decide +kernel
def pointBounds47124 : List (Nat × Nat × Nat) := [(6180620288,110918792324151,110919179024565)]
theorem point_links_checked47124 : (cuts47124.take 1).map (fun c => (6180569089-1+2*2^10*c.k,110918688762285+c.lower,110919075462634+c.upper)) = pointBounds47124 := by
 decide +kernel
def cuts47125 : List PrefixCut := [⟨56,232347704,232347839⟩,
⟨64,264407889,264408042⟩]
theorem checked47125 : checkPrefixCuts (2^48) 6180700161 10 Manual.Count131072.C047125.packed 64 cuts47125 = true := by
 decide +kernel
def pointBounds47125 : List (Nat × Nat × Nat) := [(6180814848,110919187162978,110919573863625)]
theorem point_links_checked47125 : (cuts47125.take 1).map (fun c => (6180700161-1+2*2^10*c.k,110918954815274+c.lower,110919341515786+c.upper)) = pointBounds47125 := by
 decide +kernel
def cuts47126 : List PrefixCut := [⟨64,258664294,258664443⟩]
theorem checked47126 : checkPrefixCuts (2^48) 6180831233 10 Manual.Count131072.C047126.packed 64 cuts47126 = true := by
 decide +kernel
def cuts47127 : List PrefixCut := [⟨23,95677093,95677151⟩,
⟨64,263804702,263804855⟩]
theorem checked47127 : checkPrefixCuts (2^48) 6180962305 10 Manual.Count131072.C047127.packed 64 cuts47127 = true := by
 decide +kernel
def pointBounds47127 : List (Nat × Nat × Nat) := [(6181009408,110919573564550,110919960265422)]
theorem point_links_checked47127 : (cuts47127.take 1).map (fun c => (6180962305-1+2*2^10*c.k,110919477887457+c.lower,110919864588271+c.upper)) = pointBounds47127 := by
 decide +kernel
def cuts47128 : List PrefixCut := [⟨54,221495056,221495190⟩,
⟨64,264891962,264892121⟩]
theorem checked47128 : checkPrefixCuts (2^48) 6181093377 10 Manual.Count131072.C047128.packed 64 cuts47128 = true := by
 decide +kernel
def pointBounds47128 : List (Nat × Nat × Nat) := [(6181203968,110919963187215,110920349888316)]
theorem point_links_checked47128 : (cuts47128.take 1).map (fun c => (6181093377-1+2*2^10*c.k,110919741692159+c.lower,110920128393126+c.upper)) = pointBounds47128 := by
 decide +kernel
def cuts47129 : List PrefixCut := [⟨64,262336337,262336488⟩]
theorem checked47129 : checkPrefixCuts (2^48) 6181224449 10 Manual.Count131072.C047129.packed 64 cuts47129 = true := by
 decide +kernel
def cuts47130 : List PrefixCut := [⟨21,84787944,84787993⟩,
⟨64,260919143,260919292⟩]
theorem checked47130 : checkPrefixCuts (2^48) 6181355521 10 Manual.Count131072.C047130.packed 64 cuts47130 = true := by
 decide +kernel
def pointBounds47130 : List (Nat × Nat × Nat) := [(6181398528,110920353708402,110920740409728)]
theorem point_links_checked47130 : (cuts47130.take 1).map (fun c => (6181355521-1+2*2^10*c.k,110920268920458+c.lower,110920655621735+c.upper)) = pointBounds47130 := by
 decide +kernel
def cuts47131 : List PrefixCut := [⟨52,214832979,214833105⟩,
⟨64,265967966,265968122⟩]
theorem checked47131 : checkPrefixCuts (2^48) 6181486593 10 Manual.Count131072.C047131.packed 64 cuts47131 = true := by
 decide +kernel
def pointBounds47131 : List (Nat × Nat × Nat) := [(6181593088,110920744672580,110921131374132)]
theorem point_links_checked47131 : (cuts47131.take 1).map (fun c => (6181486593-1+2*2^10*c.k,110920529839601+c.lower,110920916541027+c.upper)) = pointBounds47131 := by
 decide +kernel
def cuts47132 : List PrefixCut := [⟨64,266053390,266053544⟩]
theorem checked47132 : checkPrefixCuts (2^48) 6181617665 10 Manual.Count131072.C047132.packed 64 cuts47132 = true := by
 decide +kernel
def cuts47133 : List PrefixCut := [⟨19,80639071,80639116⟩,
⟨64,266093316,266093470⟩]
theorem checked47133 : checkPrefixCuts (2^48) 6181748737 10 Manual.Count131072.C047133.packed 64 cuts47133 = true := by
 decide +kernel
def pointBounds47133 : List (Nat × Nat × Nat) := [(6181787648,110921142500028,110921529201809)]
theorem point_links_checked47133 : (cuts47133.take 1).map (fun c => (6181748737-1+2*2^10*c.k,110921061860957+c.lower,110921448562693+c.upper)) = pointBounds47133 := by
 decide +kernel
def cuts47134 : List PrefixCut := [⟨50,208308329,208308448⟩,
⟨64,266588504,266588660⟩]
theorem checked47134 : checkPrefixCuts (2^48) 6181879809 10 Manual.Count131072.C047134.packed 64 cuts47134 = true := by
 decide +kernel
def pointBounds47134 : List (Nat × Nat × Nat) := [(6181982208,110921536262602,110921922964611)]
theorem point_links_checked47134 : (cuts47134.take 1).map (fun c => (6181879809-1+2*2^10*c.k,110921327954273+c.lower,110921714656163+c.upper)) = pointBounds47134 := by
 decide +kernel
def cuts47135 : List PrefixCut := [⟨64,268221969,268222117⟩]
theorem checked47135 : checkPrefixCuts (2^48) 6182010881 10 Manual.Count131072.C047135.packed 64 cuts47135 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000222
