import PlattAssemblyKernel
import PlattCertificates.Count131072.C012912
import PlattCertificates.Count131072.C012913
import PlattCertificates.Count131072.C012914
import PlattCertificates.Count131072.C012915
import PlattCertificates.Count131072.C012916
import PlattCertificates.Count131072.C012917
import PlattCertificates.Count131072.C012918
import PlattCertificates.Count131072.C012919
import PlattCertificates.Count131072.C012920
import PlattCertificates.Count131072.C012921
import PlattCertificates.Count131072.C012922
import PlattCertificates.Count131072.C012923
import PlattCertificates.Count131072.C012924
import PlattCertificates.Count131072.C012925
import PlattCertificates.Count131072.C012926
import PlattCertificates.Count131072.C012927
import PlattCertificates.Count131072.C012928
import PlattCertificates.Count131072.C012929
import PlattCertificates.Count131072.C012930
import PlattCertificates.Count131072.C012931
import PlattCertificates.Count131072.C012932
import PlattCertificates.Count131072.C012933
import PlattCertificates.Count131072.C012934
import PlattCertificates.Count131072.C012935
import PlattCertificates.Count131072.C012936
import PlattCertificates.Count131072.C012937
import PlattCertificates.Count131072.C012938
import PlattCertificates.Count131072.C012939
import PlattCertificates.Count131072.C012940
import PlattCertificates.Count131072.C012941
import PlattCertificates.Count131072.C012942
import PlattCertificates.Count131072.C012943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts12912 : List PrefixCut := [⟨34,273783787,273783985⟩,
⟨86,686108114,686108613⟩,
⟨128,1021101770,1021102510⟩]
theorem checked12912 : checkPrefixCuts (2^48) 1696333825 9 Manual.Count131072.C012912.packed 128 cuts12912 = true := by
 decide +kernel
def pointBounds12912 : List (Nat × Nat × Nat) := [(1696368640,94295072918853,94295449578799),(1696421888,94295485243180,94295861903427)]
theorem point_links_checked12912 : (cuts12912.take 2).map (fun c => (1696333825-1+2*2^9*c.k,94294799135066+c.lower,94295175794814+c.upper)) = pointBounds12912 := by
 decide +kernel
def cuts12913 : List PrefixCut := [⟨10,83456743,83456803⟩,
⟨62,502889518,502889882⟩,
⟨114,922972686,922973359⟩,
⟨128,1034129949,1034130705⟩]
theorem checked12913 : checkPrefixCuts (2^48) 1696464897 9 Manual.Count131072.C012913.packed 128 cuts12913 = true := by
 decide +kernel
def pointBounds12913 : List (Nat × Nat × Nat) := [(1696475136,94295903693579,94296280354127),(1696528384,94296323126354,94296699787206),(1696581632,94296743209522,94297119870683)]
theorem point_links_checked12913 : (cuts12913.take 3).map (fun c => (1696464897-1+2*2^9*c.k,94295820236836+c.lower,94296196897324+c.upper)) = pointBounds12913 := by
 decide +kernel
def cuts12914 : List PrefixCut := [⟨38,296801820,296802036⟩,
⟨90,705411665,705412174⟩,
⟨128,1011985136,1011985867⟩]
theorem checked12914 : checkPrefixCuts (2^48) 1696595969 9 Manual.Count131072.C012914.packed 128 cuts12914 = true := by
 decide +kernel
def pointBounds12914 : List (Nat × Nat × Nat) := [(1696634880,94297151168605,94297527830065),(1696688128,94297559778450,94297936440203)]
theorem point_links_checked12914 : (cuts12914.take 2).map (fun c => (1696595969-1+2*2^9*c.k,94296854366785+c.lower,94297231028029+c.upper)) = pointBounds12914 := by
 decide +kernel
def cuts12915 : List PrefixCut := [⟨14,113802002,113802085⟩,
⟨66,525372230,525372615⟩,
⟨118,940744766,940745455⟩,
⟨128,1020035662,1020036408⟩]
theorem checked12915 : checkPrefixCuts (2^48) 1696727041 9 Manual.Count131072.C012915.packed 128 cuts12915 = true := by
 decide +kernel
def pointBounds12915 : List (Nat × Nat × Nat) := [(1696741376,94297980153923,94298356815981),(1696794624,94298391724151,94298768386511),(1696847872,94298807096687,94299183759351)]
theorem point_links_checked12915 : (cuts12915.take 3).map (fun c => (1696727041-1+2*2^9*c.k,94297866351921+c.lower,94298243013896+c.upper)) = pointBounds12915 := by
 decide +kernel
def cuts12916 : List PrefixCut := [⟨42,343533132,343533379⟩,
⟨94,759211428,759211978⟩,
⟨128,1030407076,1030407826⟩]
theorem checked12916 : checkPrefixCuts (2^48) 1696858113 9 Manual.Count131072.C012916.packed 128 cuts12916 = true := by
 decide +kernel
def pointBounds12916 : List (Nat × Nat × Nat) := [(1696901120,94299229920715,94299606583683),(1696954368,94299645599011,94300022262282)]
theorem point_links_checked12916 : (cuts12916.take 2).map (fun c => (1696858113-1+2*2^9*c.k,94298886387583+c.lower,94299263050304+c.upper)) = pointBounds12916 := by
 decide +kernel
def cuts12917 : List PrefixCut := [⟨18,140654635,140654739⟩,
⟨70,557301959,557302366⟩,
⟨122,966306932,966307637⟩,
⟨128,1017390183,1017390925⟩]
theorem checked12917 : checkPrefixCuts (2^48) 1696989185 9 Manual.Count131072.C012917.packed 128 cuts12917 = true := by
 decide +kernel
def pointBounds12917 : List (Nat × Nat × Nat) := [(1697007616,94300057449294,94300434112869),(1697060864,94300474096618,94300850760496),(1697114112,94300883101591,94301259765767)]
theorem point_links_checked12917 : (cuts12917.take 3).map (fun c => (1696989185-1+2*2^9*c.k,94299916794659+c.lower,94300293458130+c.upper)) = pointBounds12917 := by
 decide +kernel
def cuts12918 : List PrefixCut := [⟨46,368357587,368357850⟩,
⟨98,790106968,790107536⟩,
⟨128,1020628857,1020629597⟩]
theorem checked12918 : checkPrefixCuts (2^48) 1697120257 9 Manual.Count131072.C012918.packed 128 cuts12918 = true := by
 decide +kernel
def pointBounds12918 : List (Nat × Nat × Nat) := [(1697167360,94301302542429,94301679206905),(1697220608,94301724291810,94302100956591)]
theorem point_links_checked12918 : (cuts12918.take 2).map (fun c => (1697120257-1+2*2^9*c.k,94300934184842+c.lower,94301310849055+c.upper)) = pointBounds12918 := by
 decide +kernel
def cuts12919 : List PrefixCut := [⟨22,173634990,173635116⟩,
⟨74,600333178,600333613⟩,
⟨126,1014082966,1014083706⟩,
⟨128,1030168368,1030169120⟩]
theorem checked12919 : checkPrefixCuts (2^48) 1697251329 9 Manual.Count131072.C012919.packed 128 cuts12919 = true := by
 decide +kernel
def pointBounds12919 : List (Nat × Nat × Nat) := [(1697273856,94302128448689,94302505113768),(1697327104,94302555146877,94302931812265),(1697380352,94302968896665,94303345562358)]
theorem point_links_checked12919 : (cuts12919.take 3).map (fun c => (1697251329-1+2*2^9*c.k,94301954813699+c.lower,94302331478652+c.upper)) = pointBounds12919 := by
 decide +kernel
def cuts12920 : List PrefixCut := [⟨50,397817323,397817609⟩,
⟨102,806234845,806235435⟩,
⟨128,1015496272,1015497014⟩]
theorem checked12920 : checkPrefixCuts (2^48) 1697382401 9 Manual.Count131072.C012920.packed 128 cuts12920 = true := by
 decide +kernel
def pointBounds12920 : List (Nat × Nat × Nat) := [(1697433600,94303382799390,94303759465381),(1697486848,94303791216912,94304167883207)]
theorem point_links_checked12920 : (cuts12920.take 2).map (fun c => (1697382401-1+2*2^9*c.k,94302984982067+c.lower,94303361647772+c.upper)) = pointBounds12920 := by
 decide +kernel
def cuts12921 : List PrefixCut := [⟨26,207268368,207268519⟩,
⟨78,618810702,618811154⟩,
⟨128,1014754767,1014755507⟩]
theorem checked12921 : checkPrefixCuts (2^48) 1697513473 9 Manual.Count131072.C012921.packed 128 cuts12921 = true := by
 decide +kernel
def pointBounds12921 : List (Nat × Nat × Nat) := [(1697540096,94304207746707,94304584413305),(1697593344,94304619289041,94304995955940)]
theorem point_links_checked12921 : (cuts12921.take 2).map (fun c => (1697513473-1+2*2^9*c.k,94304000478339+c.lower,94304377144786+c.upper)) = pointBounds12921 := by
 decide +kernel
def cuts12922 : List PrefixCut := [⟨2,14922278,14922290⟩,
⟨54,430583856,430584172⟩,
⟨106,849714027,849714649⟩,
⟨128,1022468768,1022469515⟩]
theorem checked12922 : checkPrefixCuts (2^48) 1697644545 9 Manual.Count131072.C012922.packed 128 cuts12922 = true := by
 decide +kernel
def pointBounds12922 : List (Nat × Nat × Nat) := [(1697646592,94305030155384,94305406822583),(1697699840,94305445816962,94305822484465),(1697753088,94305864947133,94306241614942)]
theorem point_links_checked12922 : (cuts12922.take 3).map (fun c => (1697644545-1+2*2^9*c.k,94305015233106+c.lower,94305391900293+c.upper)) = pointBounds12922 := by
 decide +kernel
def cuts12923 : List PrefixCut := [⟨30,234757101,234757273⟩,
⟨82,648058630,648059102⟩,
⟨128,1015758460,1015759198⟩]
theorem checked12923 : checkPrefixCuts (2^48) 1697775617 9 Manual.Count131072.C012923.packed 128 cuts12923 = true := by
 decide +kernel
def pointBounds12923 : List (Nat × Nat × Nat) := [(1697806336,94306272458975,94306649127081),(1697859584,94306685760504,94307062428910)]
theorem point_links_checked12923 : (cuts12923.take 2).map (fun c => (1697775617-1+2*2^9*c.k,94306037701874+c.lower,94306414369808+c.upper)) = pointBounds12923 := by
 decide +kernel
def cuts12924 : List PrefixCut := [⟨6,46417642,46417677⟩,
⟨58,464997971,464998306⟩,
⟨110,871961387,871962020⟩,
⟨128,1011370331,1011371066⟩]
theorem checked12924 : checkPrefixCuts (2^48) 1697906689 9 Manual.Count131072.C012924.packed 128 cuts12924 = true := by
 decide +kernel
def pointBounds12924 : List (Nat × Nat × Nat) := [(1697912832,94307099877976,94307476546683),(1697966080,94307518458305,94307895127312),(1698019328,94307925421721,94308302091026)]
theorem point_links_checked12924 : (cuts12924.take 3).map (fun c => (1697906689-1+2*2^9*c.k,94307053460334+c.lower,94307430129006+c.upper)) = pointBounds12924 := by
 decide +kernel
def cuts12925 : List PrefixCut := [⟨34,275498287,275498487⟩,
⟨86,688734955,688735453⟩,
⟨128,1020243080,1020243817⟩]
theorem checked12925 : checkPrefixCuts (2^48) 1698037761 9 Manual.Count131072.C012925.packed 128 cuts12925 = true := by
 decide +kernel
def pointBounds12925 : List (Nat × Nat × Nat) := [(1698072576,94308340328952,94308716998559),(1698125824,94308753565620,94309130235525)]
theorem point_links_checked12925 : (cuts12925.take 2).map (fun c => (1698037761-1+2*2^9*c.k,94308064830665+c.lower,94308441500072+c.upper)) = pointBounds12925 := by
 decide +kernel
def cuts12926 : List PrefixCut := [⟨10,80886739,80886796⟩,
⟨62,506031408,506031769⟩,
⟨114,932157112,932157782⟩,
⟨128,1049666708,1049667462⟩]
theorem checked12926 : checkPrefixCuts (2^48) 1698168833 9 Manual.Count131072.C012926.packed 128 cuts12926 = true := by
 decide +kernel
def pointBounds12926 : List (Nat × Nat × Nat) := [(1698179072,94309165960484,94309542630685),(1698232320,94309591105153,94309967775658),(1698285568,94310017230857,94310393901671)]
theorem point_links_checked12926 : (cuts12926.take 3).map (fun c => (1698168833-1+2*2^9*c.k,94309085073745+c.lower,94309461743889+c.upper)) = pointBounds12926 := by
 decide +kernel
def cuts12927 : List PrefixCut := [⟨38,303464980,303465200⟩,
⟨90,725089235,725089764⟩,
⟨128,1026383391,1026384137⟩]
theorem checked12927 : checkPrefixCuts (2^48) 1698299905 9 Manual.Count131072.C012927.packed 128 cuts12927 = true := by
 decide +kernel
def pointBounds12927 : List (Nat × Nat × Nat) := [(1698338816,94310438205433,94310814876551),(1698392064,94310859829688,94311236501115)]
theorem point_links_checked12927 : (cuts12927.take 2).map (fun c => (1698299905-1+2*2^9*c.k,94310134740453+c.lower,94310511411351+c.upper)) = pointBounds12927 := by
 decide +kernel
def cuts12928 : List PrefixCut := [⟨14,109544691,109544768⟩,
⟨66,531639623,531640013⟩,
⟨118,932012407,932013086⟩,
⟨128,1012052335,1012053073⟩]
theorem checked12928 : checkPrefixCuts (2^48) 1698430977 9 Manual.Count131072.C012928.packed 128 cuts12928 = true := by
 decide +kernel
def pointBounds12928 : List (Nat × Nat × Nat) := [(1698445312,94311270668535,94311647340256),(1698498560,94311692763467,94312069435501),(1698551808,94312093136251,94312469808574)]
theorem point_links_checked12928 : (cuts12928.take 3).map (fun c => (1698430977-1+2*2^9*c.k,94311161123844+c.lower,94311537795488+c.upper)) = pointBounds12928 := by
 decide +kernel
def cuts12929 : List PrefixCut := [⟨42,335565789,335566032⟩,
⟨94,752484082,752484633⟩,
⟨128,1022579243,1022579989⟩]
theorem checked12929 : checkPrefixCuts (2^48) 1698562049 9 Manual.Count131072.C012929.packed 128 cuts12929 = true := by
 decide +kernel
def pointBounds12929 : List (Nat × Nat × Nat) := [(1698605056,94312508741968,94312885414593),(1698658304,94312925660261,94313302333194)]
theorem point_links_checked12929 : (cuts12929.take 2).map (fun c => (1698562049-1+2*2^9*c.k,94312173176179+c.lower,94312549848561+c.upper)) = pointBounds12929 := by
 decide +kernel
def cuts12930 : List PrefixCut := [⟨18,140844930,140845034⟩,
⟨70,554754610,554755014⟩,
⟨122,967988553,967989259⟩,
⟨128,1013718535,1013719275⟩]
theorem checked12930 : checkPrefixCuts (2^48) 1698693121 9 Manual.Count131072.C012930.packed 128 cuts12930 = true := by
 decide +kernel
def pointBounds12930 : List (Nat × Nat × Nat) := [(1698711552,94313336600352,94313713273584),(1698764800,94313750510032,94314127183564),(1698818048,94314163743975,94314540417809)]
theorem point_links_checked12930 : (cuts12930.take 3).map (fun c => (1698693121-1+2*2^9*c.k,94313195755422+c.lower,94313572428550+c.upper)) = pointBounds12930 := by
 decide +kernel
def cuts12931 : List PrefixCut := [⟨46,364674398,364674665⟩,
⟨98,776888445,776889016⟩,
⟨128,1023581157,1023581906⟩]
theorem checked12931 : checkPrefixCuts (2^48) 1698824193 9 Manual.Count131072.C012931.packed 128 cuts12931 = true := by
 decide +kernel
def pointBounds12931 : List (Nat × Nat × Nat) := [(1698871296,94314574148355,94314950822490),(1698924544,94314986362402,94315363036841)]
theorem point_links_checked12931 : (cuts12931.take 2).map (fun c => (1698824193-1+2*2^9*c.k,94314209473957+c.lower,94314586147825+c.upper)) = pointBounds12931 := by
 decide +kernel
def cuts12932 : List PrefixCut := [⟨22,168987645,168987768⟩,
⟨74,585648917,585649348⟩,
⟨126,991031878,991032606⟩,
⟨128,1007432475,1007433215⟩]
theorem checked12932 : checkPrefixCuts (2^48) 1698955265 9 Manual.Count131072.C012932.packed 128 cuts12932 = true := by
 decide +kernel
def pointBounds12932 : List (Nat × Nat × Nat) := [(1698977792,94315402042759,94315778717499),(1699031040,94315818704031,94316195379079),(1699084288,94316224086992,94316600762337)]
theorem point_links_checked12932 : (cuts12932.take 3).map (fun c => (1698955265-1+2*2^9*c.k,94315233055114+c.lower,94315609729731+c.upper)) = pointBounds12932 := by
 decide +kernel
def cuts12933 : List PrefixCut := [⟨50,391785889,391786178⟩,
⟨102,803107042,803107636⟩,
⟨128,1009342564,1009343307⟩]
theorem checked12933 : checkPrefixCuts (2^48) 1699086337 9 Manual.Count131072.C012933.packed 128 cuts12933 = true := by
 decide +kernel
def pointBounds12933 : List (Nat × Nat × Nat) := [(1699137536,94316632273478,94317008949124),(1699190784,94317043594631,94317420270582)]
theorem point_links_checked12933 : (cuts12933.take 2).map (fun c => (1699086337-1+2*2^9*c.k,94316240487589+c.lower,94316617162946+c.upper)) = pointBounds12933 := by
 decide +kernel
def cuts12934 : List PrefixCut := [⟨26,208882610,208882765⟩,
⟨78,621668761,621669218⟩,
⟨128,1014068603,1014069350⟩]
theorem checked12934 : checkPrefixCuts (2^48) 1699217409 9 Manual.Count131072.C012934.packed 128 cuts12934 = true := by
 decide +kernel
def pointBounds12934 : List (Nat × Nat × Nat) := [(1699244032,94317458712763,94317835389018),(1699297280,94317871498914,94318248175471)]
theorem point_links_checked12934 : (cuts12934.take 2).map (fun c => (1699217409-1+2*2^9*c.k,94317249830153+c.lower,94317626506253+c.upper)) = pointBounds12934 := by
 decide +kernel
def cuts12935 : List PrefixCut := [⟨2,13085310,13085319⟩,
⟨54,438102466,438102783⟩,
⟨106,856481098,856481720⟩,
⟨128,1031215741,1031216489⟩]
theorem checked12935 : checkPrefixCuts (2^48) 1699348481 9 Manual.Count131072.C012935.packed 128 cuts12935 = true := by
 decide +kernel
def pointBounds12935 : List (Nat × Nat × Nat) := [(1699350528,94318276984066,94318653660922),(1699403776,94318702001222,94319078678386),(1699457024,94319120379854,94319497057323)]
theorem point_links_checked12935 : (cuts12935.take 3).map (fun c => (1699348481-1+2*2^9*c.k,94318263898756+c.lower,94318640575603+c.upper)) = pointBounds12935 := by
 decide +kernel
def cuts12936 : List PrefixCut := [⟨30,240484142,240484312⟩,
⟨82,656352329,656352802⟩,
⟨128,1023849095,1023849829⟩]
theorem checked12936 : checkPrefixCuts (2^48) 1699479553 9 Manual.Count131072.C012936.packed 128 cuts12936 = true := by
 decide +kernel
def pointBounds12936 : List (Nat × Nat × Nat) := [(1699510272,94319535598639,94319912276404),(1699563520,94319951466826,94320328144894)]
theorem point_links_checked12936 : (cuts12936.take 2).map (fun c => (1699479553-1+2*2^9*c.k,94319295114497+c.lower,94319671792092+c.upper)) = pointBounds12936 := by
 decide +kernel
def cuts12937 : List PrefixCut := [⟨6,47695991,47696028⟩,
⟨58,465691116,465691452⟩,
⟨110,870921715,870922344⟩,
⟨128,1014165299,1014166033⟩]
theorem checked12937 : checkPrefixCuts (2^48) 1699610625 9 Manual.Count131072.C012937.packed 128 cuts12937 = true := by
 decide +kernel
def pointBounds12937 : List (Nat × Nat × Nat) := [(1699616768,94320366659583,94320743337949),(1699670016,94320784654708,94321161333373),(1699723264,94321189885307,94321566564265)]
theorem point_links_checked12937 : (cuts12937.take 3).map (fun c => (1699610625-1+2*2^9*c.k,94320318963592+c.lower,94320695641921+c.upper)) = pointBounds12937 := by
 decide +kernel
def cuts12938 : List PrefixCut := [⟨34,271247720,271247917⟩,
⟨86,687050875,687051374⟩,
⟨128,1014087022,1014087760⟩]
theorem checked12938 : checkPrefixCuts (2^48) 1699741697 9 Manual.Count131072.C012938.packed 128 cuts12938 = true := by
 decide +kernel
def pointBounds12938 : List (Nat × Nat × Nat) := [(1699776512,94321604376611,94321981055871),(1699829760,94322020179766,94322396859328)]
theorem point_links_checked12938 : (cuts12938.take 2).map (fun c => (1699741697-1+2*2^9*c.k,94321333128891+c.lower,94321709807954+c.upper)) = pointBounds12938 := by
 decide +kernel
def cuts12939 : List PrefixCut := [⟨10,83620606,83620665⟩,
⟨62,501881338,501881700⟩,
⟨114,915492836,915493500⟩,
⟨128,1030732183,1030732929⟩]
theorem checked12939 : checkPrefixCuts (2^48) 1699872769 9 Manual.Count131072.C012939.packed 128 cuts12939 = true := by
 decide +kernel
def pointBounds12939 : List (Nat × Nat × Nat) := [(1699883008,94322430836519,94322807516379),(1699936256,94322849097251,94323225777414),(1699989504,94323262708749,94323639389214)]
theorem point_links_checked12939 : (cuts12939.take 3).map (fun c => (1699872769-1+2*2^9*c.k,94322347215913+c.lower,94322723895714+c.upper)) = pointBounds12939 := by
 decide +kernel
def cuts12940 : List PrefixCut := [⟨38,305147662,305147884⟩,
⟨90,716415403,716415928⟩,
⟨128,1033135950,1033136701⟩]
theorem checked12940 : checkPrefixCuts (2^48) 1700003841 9 Manual.Count131072.C012940.packed 128 cuts12940 = true := by
 decide +kernel
def pointBounds12940 : List (Nat × Nat × Nat) := [(1700042752,94323683095758,94324059776527),(1700096000,94324094363499,94324471044571)]
theorem point_links_checked12940 : (cuts12940.take 2).map (fun c => (1700003841-1+2*2^9*c.k,94323377948096+c.lower,94323754628643+c.upper)) = pointBounds12940 := by
 decide +kernel
def cuts12941 : List PrefixCut := [⟨14,108275988,108276068⟩,
⟨66,519848989,519849370⟩,
⟨118,939686657,939687346⟩,
⟨128,1019811922,1019812670⟩]
theorem checked12941 : checkPrefixCuts (2^48) 1700134913 9 Manual.Count131072.C012941.packed 128 cuts12941 = true := by
 decide +kernel
def pointBounds12941 : List (Nat × Nat × Nat) := [(1700149248,94324519360034,94324896041412),(1700202496,94324930933035,94325307614714),(1700255744,94325350770703,94325727452690)]
theorem point_links_checked12941 : (cuts12941.take 3).map (fun c => (1700134913-1+2*2^9*c.k,94324411084046+c.lower,94324787765344+c.upper)) = pointBounds12941 := by
 decide +kernel
def cuts12942 : List PrefixCut := [⟨42,340361393,340361640⟩,
⟨94,755868767,755869317⟩,
⟨128,1021720347,1021721093⟩]
theorem checked12942 : checkPrefixCuts (2^48) 1700265985 9 Manual.Count131072.C012942.packed 128 cuts12942 = true := by
 decide +kernel
def pointBounds12942 : List (Nat × Nat × Nat) := [(1700308992,94325771257361,94326147939654),(1700362240,94326186764735,94326563447331)]
theorem point_links_checked12942 : (cuts12942.take 2).map (fun c => (1700265985-1+2*2^9*c.k,94325430895968+c.lower,94325807578014+c.upper)) = pointBounds12942 := by
 decide +kernel
def cuts12943 : List PrefixCut := [⟨18,142193624,142193726⟩,
⟨70,553702294,553702696⟩,
⟨122,959239125,959239830⟩,
⟨128,1008233737,1008234476⟩]
theorem checked12943 : checkPrefixCuts (2^48) 1700397057 9 Manual.Count131072.C012943.packed 128 cuts12943 = true := by
 decide +kernel
def pointBounds12943 : List (Nat × Nat × Nat) := [(1700415488,94326594809939,94326971492833),(1700468736,94327006318609,94327383001803),(1700521984,94327411855440,94327788538937)]
theorem point_links_checked12943 : (cuts12943.take 3).map (fun c => (1700397057-1+2*2^9*c.k,94326452616315+c.lower,94326829299107+c.upper)) = pointBounds12943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000091
