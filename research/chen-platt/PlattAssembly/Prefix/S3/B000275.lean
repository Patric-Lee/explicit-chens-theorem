import PlattAssemblyKernel
import PlattCertificates.Count131072.C028800
import PlattCertificates.Count131072.C028801
import PlattCertificates.Count131072.C028802
import PlattCertificates.Count131072.C028803
import PlattCertificates.Count131072.C028804
import PlattCertificates.Count131072.C028805
import PlattCertificates.Count131072.C028806
import PlattCertificates.Count131072.C028807
import PlattCertificates.Count131072.C028808
import PlattCertificates.Count131072.C028809
import PlattCertificates.Count131072.C028810
import PlattCertificates.Count131072.C028811
import PlattCertificates.Count131072.C028812
import PlattCertificates.Count131072.C028813
import PlattCertificates.Count131072.C028814
import PlattCertificates.Count131072.C028815
import PlattCertificates.Count131072.C028816
import PlattCertificates.Count131072.C028817
import PlattCertificates.Count131072.C028818
import PlattCertificates.Count131072.C028819
import PlattCertificates.Count131072.C028820
import PlattCertificates.Count131072.C028821
import PlattCertificates.Count131072.C028822
import PlattCertificates.Count131072.C028823
import PlattCertificates.Count131072.C028824
import PlattCertificates.Count131072.C028825
import PlattCertificates.Count131072.C028826
import PlattCertificates.Count131072.C028827
import PlattCertificates.Count131072.C028828
import PlattCertificates.Count131072.C028829
import PlattCertificates.Count131072.C028830
import PlattCertificates.Count131072.C028831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000275
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28800 : List PrefixCut := [⟨75,261449498,261449645⟩,
⟨128,441258075,441258326⟩]
theorem checked28800 : checkPrefixCuts (2^48) 3778805761 9 Manual.Count131072.C028800.packed 128 cuts28800 = true := by
 decide +kernel
def pointBounds28800 : List (Nat × Nat × Nat) := [(3778882560,104708288331163,104708671360998)]
theorem point_links_checked28800 : (cuts28800.take 1).map (fun c => (3778805761-1+2*2^9*c.k,104708026881665+c.lower,104708409911353+c.upper)) = pointBounds28800 := by
 decide +kernel
def cuts28801 : List PrefixCut := [⟨63,215334902,215335022⟩,
⟨128,438188890,438189138⟩]
theorem checked28801 : checkPrefixCuts (2^48) 3778936833 9 Manual.Count131072.C028801.packed 128 cuts28801 = true := by
 decide +kernel
def pointBounds28801 : List (Nat × Nat × Nat) := [(3779001344,104708683474642,104709066504701)]
theorem point_links_checked28801 : (cuts28801.take 1).map (fun c => (3778936833-1+2*2^9*c.k,104708468139740+c.lower,104708851169679+c.upper)) = pointBounds28801 := by
 decide +kernel
def cuts28802 : List PrefixCut := [⟨51,176224664,176224763⟩,
⟨128,445994208,445994455⟩]
theorem checked28802 : checkPrefixCuts (2^48) 3779067905 9 Manual.Count131072.C028802.packed 128 cuts28802 = true := by
 decide +kernel
def pointBounds28802 : List (Nat × Nat × Nat) := [(3779120128,104709082553294,104709465583580)]
theorem point_links_checked28802 : (cuts28802.take 1).map (fun c => (3779067905-1+2*2^9*c.k,104708906328630+c.lower,104709289358817+c.upper)) = pointBounds28802 := by
 decide +kernel
def cuts28803 : List PrefixCut := [⟨39,135031596,135031670⟩,
⟨128,444340236,444340482⟩]
theorem checked28803 : checkPrefixCuts (2^48) 3779198977 9 Manual.Count131072.C028803.packed 128 cuts28803 = true := by
 decide +kernel
def pointBounds28803 : List (Nat × Nat × Nat) := [(3779238912,104709487354434,104709870384942)]
theorem point_links_checked28803 : (cuts28803.take 1).map (fun c => (3779198977-1+2*2^9*c.k,104709352322838+c.lower,104709735353272+c.upper)) = pointBounds28803 := by
 decide +kernel
def cuts28804 : List PrefixCut := [⟨27,92426189,92426241⟩,
⟨128,437175112,437175365⟩]
theorem checked28804 : checkPrefixCuts (2^48) 3779330049 9 Manual.Count131072.C028804.packed 128 cuts28804 = true := by
 decide +kernel
def pointBounds28804 : List (Nat × Nat × Nat) := [(3779357696,104709889089263,104710272119995)]
theorem point_links_checked28804 : (cuts28804.take 1).map (fun c => (3779330049-1+2*2^9*c.k,104709796663074+c.lower,104710179693754+c.upper)) = pointBounds28804 := by
 decide +kernel
def cuts28805 : List PrefixCut := [⟨15,50121489,50121516⟩,
⟨128,441330376,441330623⟩]
theorem checked28805 : checkPrefixCuts (2^48) 3779461121 9 Manual.Count131072.C028805.packed 128 cuts28805 = true := by
 decide +kernel
def pointBounds28805 : List (Nat × Nat × Nat) := [(3779476480,104710283959675,104710666990635)]
theorem point_links_checked28805 : (cuts28805.take 1).map (fun c => (3779461121-1+2*2^9*c.k,104710233838186+c.lower,104710616869119+c.upper)) = pointBounds28805 := by
 decide +kernel
def cuts28806 : List PrefixCut := [⟨3,10202700,10202705⟩,
⟨119,414282685,414282913⟩,
⟨128,444442955,444443200⟩]
theorem checked28806 : checkPrefixCuts (2^48) 3779592193 9 Manual.Count131072.C028806.packed 128 cuts28806 = true := by
 decide +kernel
def pointBounds28806 : List (Nat × Nat × Nat) := [(3779595264,104710685371262,104711068402447),(3779714048,104711089451247,104711472482655)]
theorem point_links_checked28806 : (cuts28806.take 2).map (fun c => (3779592193-1+2*2^9*c.k,104710675168562+c.lower,104711058199742+c.upper)) = pointBounds28806 := by
 decide +kernel
def cuts28807 : List PrefixCut := [⟨107,365492054,365492260⟩,
⟨128,438321113,438321359⟩]
theorem checked28807 : checkPrefixCuts (2^48) 3779723265 9 Manual.Count131072.C028807.packed 128 cuts28807 = true := by
 decide +kernel
def pointBounds28807 : List (Nat × Nat × Nat) := [(3779832832,104711485103571,104711868135202)]
theorem point_links_checked28807 : (cuts28807.take 1).map (fun c => (3779723265-1+2*2^9*c.k,104711119611517+c.lower,104711502642942+c.upper)) = pointBounds28807 := by
 decide +kernel
def cuts28808 : List PrefixCut := [⟨95,320800267,320800447⟩,
⟨128,438305840,438306087⟩]
theorem checked28808 : checkPrefixCuts (2^48) 3779854337 9 Manual.Count131072.C028808.packed 128 cuts28808 = true := by
 decide +kernel
def pointBounds28808 : List (Nat × Nat × Nat) := [(3779951616,104711878732897,104712261764748)]
theorem point_links_checked28808 : (cuts28808.take 1).map (fun c => (3779854337-1+2*2^9*c.k,104711557932630+c.lower,104711940964301+c.upper)) = pointBounds28808 := by
 decide +kernel
def cuts28809 : List PrefixCut := [⟨83,287057594,287057756⟩,
⟨128,445364705,445364954⟩]
theorem checked28809 : checkPrefixCuts (2^48) 3779985409 9 Manual.Count131072.C028809.packed 128 cuts28809 = true := by
 decide +kernel
def pointBounds28809 : List (Nat × Nat × Nat) := [(3780070400,104712283296064,104712666328144)]
theorem point_links_checked28809 : (cuts28809.take 1).map (fun c => (3779985409-1+2*2^9*c.k,104711996238470+c.lower,104712379270388+c.upper)) = pointBounds28809 := by
 decide +kernel
def cuts28810 : List PrefixCut := [⟨71,246317813,246317951⟩,
⟨128,443562255,443562508⟩]
theorem checked28810 : checkPrefixCuts (2^48) 3780116481 9 Manual.Count131072.C028810.packed 128 cuts28810 = true := by
 decide +kernel
def pointBounds28810 : List (Nat × Nat × Nat) := [(3780189184,104712687920988,104713070953293)]
theorem point_links_checked28810 : (cuts28810.take 1).map (fun c => (3780116481-1+2*2^9*c.k,104712441603175+c.lower,104712824635342+c.upper)) = pointBounds28810 := by
 decide +kernel
def cuts28811 : List PrefixCut := [⟨59,209229198,209229314⟩,
⟨128,451216055,451216305⟩]
theorem checked28811 : checkPrefixCuts (2^48) 3780247553 9 Manual.Count131072.C028811.packed 128 cuts28811 = true := by
 decide +kernel
def pointBounds28811 : List (Nat × Nat × Nat) := [(3780307968,104713094394628,104713477427164)]
theorem point_links_checked28811 : (cuts28811.take 1).map (fun c => (3780247553-1+2*2^9*c.k,104712885165430+c.lower,104713268197850+c.upper)) = pointBounds28811 := by
 decide +kernel
def cuts28812 : List PrefixCut := [⟨47,161942506,161942597⟩,
⟨128,437053886,437054133⟩]
theorem checked28812 : checkPrefixCuts (2^48) 3780378625 9 Manual.Count131072.C028812.packed 128 cuts28812 = true := by
 decide +kernel
def pointBounds28812 : List (Nat × Nat × Nat) := [(3780426752,104713498323991,104713881356752)]
theorem point_links_checked28812 : (cuts28812.take 1).map (fun c => (3780378625-1+2*2^9*c.k,104713336381485+c.lower,104713719414155+c.upper)) = pointBounds28812 := by
 decide +kernel
def cuts28813 : List PrefixCut := [⟨35,121210896,121210965⟩,
⟨128,447610962,447611211⟩]
theorem checked28813 : checkPrefixCuts (2^48) 3780509697 9 Manual.Count131072.C028813.packed 128 cuts28813 = true := by
 decide +kernel
def pointBounds28813 : List (Nat × Nat × Nat) := [(3780545536,104713894646267,104714277679253)]
theorem point_links_checked28813 : (cuts28813.take 1).map (fun c => (3780509697-1+2*2^9*c.k,104713773435371+c.lower,104714156468288+c.upper)) = pointBounds28813 := by
 decide +kernel
def cuts28814 : List PrefixCut := [⟨23,78025077,78025122⟩,
⟨128,443351788,443352038⟩]
theorem checked28814 : checkPrefixCuts (2^48) 3780640769 9 Manual.Count131072.C028814.packed 128 cuts28814 = true := by
 decide +kernel
def pointBounds28814 : List (Nat × Nat × Nat) := [(3780664320,104714299071410,104714682104621)]
theorem point_links_checked28814 : (cuts28814.take 1).map (fun c => (3780640769-1+2*2^9*c.k,104714221046333+c.lower,104714604079499+c.upper)) = pointBounds28814 := by
 decide +kernel
def cuts28815 : List PrefixCut := [⟨11,37820059,37820080⟩,
⟨127,430605941,430606180⟩,
⟨128,434104926,434105167⟩]
theorem checked28815 : checkPrefixCuts (2^48) 3780771841 9 Manual.Count131072.C028815.packed 128 cuts28815 = true := by
 decide +kernel
def pointBounds28815 : List (Nat × Nat × Nat) := [(3780783104,104714702218180,104715085251617),(3780901888,104715095004062,104715478037717)]
theorem point_links_checked28815 : (cuts28815.take 2).map (fun c => (3780771841-1+2*2^9*c.k,104714664398121+c.lower,104715047431537+c.upper)) = pointBounds28815 := by
 decide +kernel
def cuts28816 : List PrefixCut := [⟨115,398282486,398282713⟩,
⟨128,443172234,443172486⟩]
theorem checked28816 : checkPrefixCuts (2^48) 3780902913 9 Manual.Count131072.C028816.packed 128 cuts28816 = true := by
 decide +kernel
def pointBounds28816 : List (Nat × Nat × Nat) := [(3781020672,104715496785533,104715879819417)]
theorem point_links_checked28816 : (cuts28816.take 1).map (fun c => (3780902913-1+2*2^9*c.k,104715098503047+c.lower,104715481536704+c.upper)) = pointBounds28816 := by
 decide +kernel
def cuts28817 : List PrefixCut := [⟨103,353082485,353082683⟩,
⟨128,435265970,435266216⟩]
theorem checked28817 : checkPrefixCuts (2^48) 3781033985 9 Manual.Count131072.C028817.packed 128 cuts28817 = true := by
 decide +kernel
def pointBounds28817 : List (Nat × Nat × Nat) := [(3781139456,104715894757766,104716277791873)]
theorem point_links_checked28817 : (cuts28817.take 1).map (fun c => (3781033985-1+2*2^9*c.k,104715541675281+c.lower,104715924709190+c.upper)) = pointBounds28817 := by
 decide +kernel
def cuts28818 : List PrefixCut := [⟨91,314808415,314808593⟩,
⟨128,441875967,441876220⟩]
theorem checked28818 : checkPrefixCuts (2^48) 3781165057 9 Manual.Count131072.C028818.packed 128 cuts28818 = true := by
 decide +kernel
def pointBounds28818 : List (Nat × Nat × Nat) := [(3781258240,104716291749666,104716674783999)]
theorem point_links_checked28818 : (cuts28818.take 1).map (fun c => (3781165057-1+2*2^9*c.k,104715976941251+c.lower,104716359975406+c.upper)) = pointBounds28818 := by
 decide +kernel
def cuts28819 : List PrefixCut := [⟨79,274675987,274676140⟩,
⟨128,443870488,443870735⟩]
theorem checked28819 : checkPrefixCuts (2^48) 3781296129 9 Manual.Count131072.C028819.packed 128 cuts28819 = true := by
 decide +kernel
def pointBounds28819 : List (Nat × Nat × Nat) := [(3781377024,104716693493205,104717076527766)]
theorem point_links_checked28819 : (cuts28819.take 1).map (fun c => (3781296129-1+2*2^9*c.k,104716418817218+c.lower,104716801851626+c.upper)) = pointBounds28819 := by
 decide +kernel
def cuts28820 : List PrefixCut := [⟨67,228963559,228963690⟩,
⟨128,440877700,440877947⟩]
theorem checked28820 : checkPrefixCuts (2^48) 3781427201 9 Manual.Count131072.C028820.packed 128 cuts28820 = true := by
 decide +kernel
def pointBounds28820 : List (Nat × Nat × Nat) := [(3781495808,104717091651265,104717474686051)]
theorem point_links_checked28820 : (cuts28820.take 1).map (fun c => (3781427201-1+2*2^9*c.k,104716862687706+c.lower,104717245722361+c.upper)) = pointBounds28820 := by
 decide +kernel
def cuts28821 : List PrefixCut := [⟨55,189134294,189134402⟩,
⟨128,444360689,444360942⟩]
theorem checked28821 : checkPrefixCuts (2^48) 3781558273 9 Manual.Count131072.C028821.packed 128 cuts28821 = true := by
 decide +kernel
def pointBounds28821 : List (Nat × Nat × Nat) := [(3781614592,104717492699700,104717875734710)]
theorem point_links_checked28821 : (cuts28821.take 1).map (fun c => (3781558273-1+2*2^9*c.k,104717303565406+c.lower,104717686600308+c.upper)) = pointBounds28821 := by
 decide +kernel
def cuts28822 : List PrefixCut := [⟨43,146107179,146107257⟩,
⟨128,444196407,444196651⟩]
theorem checked28822 : checkPrefixCuts (2^48) 3781689345 9 Manual.Count131072.C028822.packed 128 cuts28822 = true := by
 decide +kernel
def pointBounds28822 : List (Nat × Nat × Nat) := [(3781733376,104717894033274,104718277068507)]
theorem point_links_checked28822 : (cuts28822.take 1).map (fun c => (3781689345-1+2*2^9*c.k,104717747926095+c.lower,104718130961250+c.upper)) = pointBounds28822 := by
 decide +kernel
def cuts28823 : List PrefixCut := [⟨31,109483730,109483791⟩,
⟨128,445818519,445818766⟩]
theorem checked28823 : checkPrefixCuts (2^48) 3781820417 9 Manual.Count131072.C028823.packed 128 cuts28823 = true := by
 decide +kernel
def pointBounds28823 : List (Nat × Nat × Nat) := [(3781852160,104718301606232,104718684641692)]
theorem point_links_checked28823 : (cuts28823.take 1).map (fun c => (3781820417-1+2*2^9*c.k,104718192122502+c.lower,104718575157901+c.upper)) = pointBounds28823 := by
 decide +kernel
def cuts28824 : List PrefixCut := [⟨19,65866695,65866733⟩,
⟨128,443719120,443719367⟩]
theorem checked28824 : checkPrefixCuts (2^48) 3781951489 9 Manual.Count131072.C028824.packed 128 cuts28824 = true := by
 decide +kernel
def pointBounds28824 : List (Nat × Nat × Nat) := [(3781970944,104718703807716,104719086843400)]
theorem point_links_checked28824 : (cuts28824.take 1).map (fun c => (3781951489-1+2*2^9*c.k,104718637941021+c.lower,104719020976667+c.upper)) = pointBounds28824 := by
 decide +kernel
def cuts28825 : List PrefixCut := [⟨7,23443302,23443315⟩,
⟨123,431498907,431499147⟩,
⟨128,449136620,449136870⟩]
theorem checked28825 : checkPrefixCuts (2^48) 3782082561 9 Manual.Count131072.C028825.packed 128 cuts28825 = true := by
 decide +kernel
def pointBounds28825 : List (Nat × Nat × Nat) := [(3782089728,104719105103443,104719488139349),(3782208512,104719513159048,104719896195181)]
theorem point_links_checked28825 : (cuts28825.take 2).map (fun c => (3782082561-1+2*2^9*c.k,104719081660141+c.lower,104719464696034+c.upper)) = pointBounds28825 := by
 decide +kernel
def cuts28826 : List PrefixCut := [⟨111,383409532,383409742⟩,
⟨128,441009268,441009513⟩]
theorem checked28826 : checkPrefixCuts (2^48) 3782213633 9 Manual.Count131072.C028826.packed 128 cuts28826 = true := by
 decide +kernel
def pointBounds28826 : List (Nat × Nat × Nat) := [(3782327296,104719914206293,104720297242646)]
theorem point_links_checked28826 : (cuts28826.take 1).map (fun c => (3782213633-1+2*2^9*c.k,104719530796761+c.lower,104719913832904+c.upper)) = pointBounds28826 := by
 decide +kernel
def cuts28827 : List PrefixCut := [⟨99,342765182,342765375⟩,
⟨128,444491594,444491845⟩]
theorem checked28827 : checkPrefixCuts (2^48) 3782344705 9 Manual.Count131072.C028827.packed 128 cuts28827 = true := by
 decide +kernel
def pointBounds28827 : List (Nat × Nat × Nat) := [(3782446080,104720314571211,104720697607792)]
theorem point_links_checked28827 : (cuts28827.take 1).map (fun c => (3782344705-1+2*2^9*c.k,104719971806029+c.lower,104720354842417+c.upper)) = pointBounds28827 := by
 decide +kernel
def cuts28828 : List PrefixCut := [⟨87,299667768,299667935⟩,
⟨128,440383413,440383659⟩]
theorem checked28828 : checkPrefixCuts (2^48) 3782475777 9 Manual.Count131072.C028828.packed 128 cuts28828 = true := by
 decide +kernel
def pointBounds28828 : List (Nat × Nat × Nat) := [(3782564864,104720715965391,104721099002197)]
theorem point_links_checked28828 : (cuts28828.take 1).map (fun c => (3782475777-1+2*2^9*c.k,104720416297623+c.lower,104720799334262+c.upper)) = pointBounds28828 := by
 decide +kernel
def cuts28829 : List PrefixCut := [⟨75,259475286,259475431⟩,
⟨128,439921707,439921953⟩]
theorem checked28829 : checkPrefixCuts (2^48) 3782606849 9 Manual.Count131072.C028829.packed 128 cuts28829 = true := by
 decide +kernel
def pointBounds28829 : List (Nat × Nat × Nat) := [(3782683648,104721116156322,104721499193352)]
theorem point_links_checked28829 : (cuts28829.take 1).map (fun c => (3782606849-1+2*2^9*c.k,104720856681036+c.lower,104721239717921+c.upper)) = pointBounds28829 := by
 decide +kernel
def cuts28830 : List PrefixCut := [⟨63,217053195,217053315⟩,
⟨128,444296563,444296811⟩]
theorem checked28830 : checkPrefixCuts (2^48) 3782737921 9 Manual.Count131072.C028830.packed 128 cuts28830 = true := by
 decide +kernel
def pointBounds28830 : List (Nat × Nat × Nat) := [(3782802432,104721513655938,104721896693189)]
theorem point_links_checked28830 : (cuts28830.take 1).map (fun c => (3782737921-1+2*2^9*c.k,104721296602743+c.lower,104721679639874+c.upper)) = pointBounds28830 := by
 decide +kernel
def cuts28831 : List PrefixCut := [⟨51,175973182,175973279⟩,
⟨128,443760273,443760522⟩]
theorem checked28831 : checkPrefixCuts (2^48) 3782868993 9 Manual.Count131072.C028831.packed 128 cuts28831 = true := by
 decide +kernel
def pointBounds28831 : List (Nat × Nat × Nat) := [(3782921216,104721916872488,104722299909964)]
theorem point_links_checked28831 : (cuts28831.take 1).map (fun c => (3782868993-1+2*2^9*c.k,104721740899306+c.lower,104722123936685+c.upper)) = pointBounds28831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000275
