import PlattAssemblyKernel
import PlattCertificates.Count131072.C016912
import PlattCertificates.Count131072.C016913
import PlattCertificates.Count131072.C016914
import PlattCertificates.Count131072.C016915
import PlattCertificates.Count131072.C016916
import PlattCertificates.Count131072.C016917
import PlattCertificates.Count131072.C016918
import PlattCertificates.Count131072.C016919
import PlattCertificates.Count131072.C016920
import PlattCertificates.Count131072.C016921
import PlattCertificates.Count131072.C016922
import PlattCertificates.Count131072.C016923
import PlattCertificates.Count131072.C016924
import PlattCertificates.Count131072.C016925
import PlattCertificates.Count131072.C016926
import PlattCertificates.Count131072.C016927
import PlattCertificates.Count131072.C016928
import PlattCertificates.Count131072.C016929
import PlattCertificates.Count131072.C016930
import PlattCertificates.Count131072.C016931
import PlattCertificates.Count131072.C016932
import PlattCertificates.Count131072.C016933
import PlattCertificates.Count131072.C016934
import PlattCertificates.Count131072.C016935
import PlattCertificates.Count131072.C016936
import PlattCertificates.Count131072.C016937
import PlattCertificates.Count131072.C016938
import PlattCertificates.Count131072.C016939
import PlattCertificates.Count131072.C016940
import PlattCertificates.Count131072.C016941
import PlattCertificates.Count131072.C016942
import PlattCertificates.Count131072.C016943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000216
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16912 : List PrefixCut := [⟨24,143485841,143485932⟩,
⟨92,549851428,549851776⟩,
⟨128,764056486,764056966⟩]
theorem checked16912 : checkPrefixCuts (2^48) 2220621825 9 Manual.Count131072.C016912.packed 128 cuts16912 = true := by
 decide +kernel
def pointBounds16912 : List (Nat × Nat × Nat) := [(2220646400,97839469983375,97839849031255),(2220716032,97839876348962,97840255397099)]
theorem point_links_checked16912 : (cuts16912.take 2).map (fun c => (2220621825-1+2*2^9*c.k,97839326497534+c.lower,97839705545323+c.upper)) = pointBounds16912 := by
 decide +kernel
def cuts16913 : List PrefixCut := [⟨32,193922250,193922372⟩,
⟨100,604571706,604572078⟩,
⟨128,771109183,771109661⟩]
theorem checked16913 : checkPrefixCuts (2^48) 2220752897 9 Manual.Count131072.C016913.packed 128 cuts16913 = true := by
 decide +kernel
def pointBounds16913 : List (Nat × Nat × Nat) := [(2220785664,97840284476270,97840663524661),(2220855296,97840695125726,97841074174367)]
theorem point_links_checked16913 : (cuts16913.take 2).map (fun c => (2220752897-1+2*2^9*c.k,97840090554020+c.lower,97840469602289+c.upper)) = pointBounds16913 := by
 decide +kernel
def cuts16914 : List PrefixCut := [⟨40,238015544,238015691⟩,
⟨108,641288550,641288951⟩,
⟨128,763966227,763966702⟩]
theorem checked16914 : checkPrefixCuts (2^48) 2220883969 9 Manual.Count131072.C016914.packed 128 cuts16914 = true := by
 decide +kernel
def pointBounds16914 : List (Nat × Nat × Nat) := [(2220924928,97841099678747,97841478727641),(2220994560,97841502951753,97841882000901)]
theorem point_links_checked16914 : (cuts16914.take 2).map (fun c => (2220883969-1+2*2^9*c.k,97840861663203+c.lower,97841240711950+c.upper)) = pointBounds16914 := by
 decide +kernel
def cuts16915 : List PrefixCut := [⟨48,287679732,287679918⟩,
⟨116,706514954,706515399⟩,
⟨128,778621720,778622210⟩]
theorem checked16915 : checkPrefixCuts (2^48) 2221015041 9 Manual.Count131072.C016915.packed 128 cuts16915 = true := by
 decide +kernel
def pointBounds16915 : List (Nat × Nat × Nat) := [(2221064192,97841913309162,97842292358570),(2221133824,97842332144384,97842711194051)]
theorem point_links_checked16915 : (cuts16915.take 2).map (fun c => (2221015041-1+2*2^9*c.k,97841625629430+c.lower,97842004678652+c.upper)) = pointBounds16915 := by
 decide +kernel
def cuts16916 : List PrefixCut := [⟨56,341646385,341646599⟩,
⟨124,739800016,739800482⟩,
⟨128,764763403,764763885⟩]
theorem checked16916 : checkPrefixCuts (2^48) 2221146113 9 Manual.Count131072.C016916.packed 128 cuts16916 = true := by
 decide +kernel
def pointBounds16916 : List (Nat × Nat × Nat) := [(2221203456,97842745897535,97843124947461),(2221273088,97843144051166,97843523101344)]
theorem point_links_checked16916 : (cuts16916.take 2).map (fun c => (2221146113-1+2*2^9*c.k,97842404251150+c.lower,97842783300862+c.upper)) = pointBounds16916 := by
 decide +kernel
def cuts16917 : List PrefixCut := [⟨64,392818696,392818943⟩,
⟨128,776502536,776503029⟩]
theorem checked16917 : checkPrefixCuts (2^48) 2221277185 9 Manual.Count131072.C016917.packed 128 cuts16917 = true := by
 decide +kernel
def pointBounds16917 : List (Nat × Nat × Nat) := [(2221342720,97843561833249,97843940883690)]
theorem point_links_checked16917 : (cuts16917.take 1).map (fun c => (2221277185-1+2*2^9*c.k,97843169014553+c.lower,97843548064747+c.upper)) = pointBounds16917 := by
 decide +kernel
def cuts16918 : List PrefixCut := [⟨4,25468709,25468724⟩,
⟨72,439676739,439677013⟩,
⟨128,773795889,773796382⟩]
theorem checked16918 : checkPrefixCuts (2^48) 2221408257 9 Manual.Count131072.C016918.packed 128 cuts16918 = true := by
 decide +kernel
def pointBounds16918 : List (Nat × Nat × Nat) := [(2221412352,97843970985798,97844350036500),(2221481984,97844385193828,97844764244789)]
theorem point_links_checked16918 : (cuts16918.take 2).map (fun c => (2221408257-1+2*2^9*c.k,97843945517089+c.lower,97844324567776+c.upper)) = pointBounds16918 := by
 decide +kernel
def cuts16919 : List PrefixCut := [⟨12,70319766,70319810⟩,
⟨80,485262043,485262345⟩,
⟨128,768935642,768936121⟩]
theorem checked16919 : checkPrefixCuts (2^48) 2221539329 9 Manual.Count131072.C016919.packed 128 cuts16919 = true := by
 decide +kernel
def pointBounds16919 : List (Nat × Nat × Nat) := [(2221551616,97844789632744,97845168683968),(2221621248,97845204575021,97845583626503)]
theorem point_links_checked16919 : (cuts16919.take 2).map (fun c => (2221539329-1+2*2^9*c.k,97844719312978+c.lower,97845098364158+c.upper)) = pointBounds16919 := by
 decide +kernel
def cuts16920 : List PrefixCut := [⟨20,121120015,121120090⟩,
⟨88,528688285,528688614⟩,
⟨128,776364996,776365474⟩]
theorem checked16920 : checkPrefixCuts (2^48) 2221670401 9 Manual.Count131072.C016920.packed 128 cuts16920 = true := by
 decide +kernel
def pointBounds16920 : List (Nat × Nat × Nat) := [(2221690880,97845609368635,97845988420369),(2221760512,97846016936905,97846395988893)]
theorem point_links_checked16920 : (cuts16920.take 2).map (fun c => (2221670401-1+2*2^9*c.k,97845488248620+c.lower,97845867300279+c.upper)) = pointBounds16920 := by
 decide +kernel
def cuts16921 : List PrefixCut := [⟨28,166846615,166846718⟩,
⟨96,577683092,577683451⟩,
⟨128,767071387,767071865⟩]
theorem checked16921 : checkPrefixCuts (2^48) 2221801473 9 Manual.Count131072.C016921.packed 128 cuts16921 = true := by
 decide +kernel
def pointBounds16921 : List (Nat × Nat × Nat) := [(2221830144,97846431460231,97846810512471),(2221899776,97846842296708,97847221349204)]
theorem point_links_checked16921 : (cuts16921.take 2).map (fun c => (2221801473-1+2*2^9*c.k,97846264613616+c.lower,97846643665753+c.upper)) = pointBounds16921 := by
 decide +kernel
def cuts16922 : List PrefixCut := [⟨36,216748016,216748152⟩,
⟨104,633259065,633259463⟩,
⟨128,775006630,775007122⟩]
theorem checked16922 : checkPrefixCuts (2^48) 2221932545 9 Manual.Count131072.C016922.packed 128 cuts16922 = true := by
 decide +kernel
def pointBounds16922 : List (Nat × Nat × Nat) := [(2221969408,97847248433019,97847627485770),(2222039040,97847664944068,97848043997081)]
theorem point_links_checked16922 : (cuts16922.take 2).map (fun c => (2221932545-1+2*2^9*c.k,97847031685003+c.lower,97847410737618+c.upper)) = pointBounds16922 := by
 decide +kernel
def cuts16923 : List PrefixCut := [⟨44,267530142,267530308⟩,
⟨112,673121728,673122147⟩,
⟨128,767234377,767234853⟩]
theorem checked16923 : checkPrefixCuts (2^48) 2222063617 9 Manual.Count131072.C016923.packed 128 cuts16923 = true := by
 decide +kernel
def pointBounds16923 : List (Nat × Nat × Nat) := [(2222108672,97848074221775,97848453275048),(2222178304,97848479813361,97848858866887)]
theorem point_links_checked16923 : (cuts16923.take 2).map (fun c => (2222063617-1+2*2^9*c.k,97847806691633+c.lower,97848185744740+c.upper)) = pointBounds16923 := by
 decide +kernel
def cuts16924 : List PrefixCut := [⟨52,314126109,314126303⟩,
⟨120,719692224,719692678⟩,
⟨128,768075594,768076078⟩]
theorem checked16924 : checkPrefixCuts (2^48) 2222194689 9 Manual.Count131072.C016924.packed 128 cuts16924 = true := by
 decide +kernel
def pointBounds16924 : List (Nat × Nat × Nat) := [(2222247936,97848888052119,97849267105896),(2222317568,97849293618234,97849672672271)]
theorem point_links_checked16924 : (cuts16924.take 2).map (fun c => (2222194689-1+2*2^9*c.k,97848573926010+c.lower,97848952979593+c.upper)) = pointBounds16924 := by
 decide +kernel
def cuts16925 : List PrefixCut := [⟨60,362489566,362489791⟩,
⟨128,768030336,768030816⟩]
theorem checked16925 : checkPrefixCuts (2^48) 2222325761 9 Manual.Count131072.C016925.packed 128 cuts16925 = true := by
 decide +kernel
def pointBounds16925 : List (Nat × Nat × Nat) := [(2222387200,97849704491170,97850083545462),(2222456832,97850110031940,97850489086487)]
theorem point_links_checked16925 : (cuts16925.take 2).map (fun c => (2222325761-1+2*2^9*c.k,97849342001604+c.lower,97849721055671+c.upper)) = pointBounds16925 := by
 decide +kernel
def cuts16926 : List PrefixCut := [⟨68,412113643,412113904⟩,
⟨128,774570520,774571006⟩]
theorem checked16926 : checkPrefixCuts (2^48) 2222456833 9 Manual.Count131072.C016926.packed 128 cuts16926 = true := by
 decide +kernel
def pointBounds16926 : List (Nat × Nat × Nat) := [(2222526464,97850522145583,97850901200391)]
theorem point_links_checked16926 : (cuts16926.take 1).map (fun c => (2222456833-1+2*2^9*c.k,97850110031940+c.lower,97850489086487+c.upper)) = pointBounds16926 := by
 decide +kernel
def cuts16927 : List PrefixCut := [⟨8,47997555,47997585⟩,
⟨76,456412918,456413203⟩,
⟨128,766293391,766293876⟩]
theorem checked16927 : checkPrefixCuts (2^48) 2222587905 9 Manual.Count131072.C016927.packed 128 cuts16927 = true := by
 decide +kernel
def pointBounds16927 : List (Nat × Nat × Nat) := [(2222596096,97850932600015,97851311655078),(2222665728,97851341015378,97851720070696)]
theorem point_links_checked16927 : (cuts16927.take 2).map (fun c => (2222587905-1+2*2^9*c.k,97850884602460+c.lower,97851263657493+c.upper)) = pointBounds16927 := by
 decide +kernel
def cuts16928 : List PrefixCut := [⟨16,93329935,93329997⟩,
⟨84,505645237,505645553⟩,
⟨128,773212761,773213242⟩]
theorem checked16928 : checkPrefixCuts (2^48) 2222718977 9 Manual.Count131072.C016928.packed 128 cuts16928 = true := by
 decide +kernel
def pointBounds16928 : List (Nat × Nat × Nat) := [(2222735360,97851744225786,97852123281366),(2222804992,97852156541088,97852535596922)]
theorem point_links_checked16928 : (cuts16928.take 2).map (fun c => (2222718977-1+2*2^9*c.k,97851650895851+c.lower,97852029951369+c.upper)) = pointBounds16928 := by
 decide +kernel
def cuts16929 : List PrefixCut := [⟨24,150559780,150559875⟩,
⟨92,556771277,556771628⟩,
⟨128,774560225,774560709⟩]
theorem checked16929 : checkPrefixCuts (2^48) 2222850049 9 Manual.Count131072.C016929.packed 128 cuts16929 = true := by
 decide +kernel
def pointBounds16929 : List (Nat × Nat × Nat) := [(2222874624,97852574668392,97852953724486),(2222944256,97852980879889,97853359936239)]
theorem point_links_checked16929 : (cuts16929.take 2).map (fun c => (2222850049-1+2*2^9*c.k,97852424108612+c.lower,97852803164611+c.upper)) = pointBounds16929 := by
 decide +kernel
def cuts16930 : List PrefixCut := [⟨32,188916322,188916442⟩,
⟨100,596115293,596115668⟩,
⟨128,764764894,764765375⟩]
theorem checked16930 : checkPrefixCuts (2^48) 2222981121 9 Manual.Count131072.C016930.packed 128 cuts16930 = true := by
 decide +kernel
def pointBounds16930 : List (Nat × Nat × Nat) := [(2223013888,97853387585159,97853766641762),(2223083520,97853794784130,97854173840988)]
theorem point_links_checked16930 : (cuts16930.take 2).map (fun c => (2222981121-1+2*2^9*c.k,97853198668837+c.lower,97853577725320+c.upper)) = pointBounds16930 := by
 decide +kernel
def cuts16931 : List PrefixCut := [⟨40,235498007,235498154⟩,
⟨108,644950452,644950856⟩,
⟨128,768138201,768138680⟩]
theorem checked16931 : checkPrefixCuts (2^48) 2223112193 9 Manual.Count131072.C016931.packed 128 cuts16931 = true := by
 decide +kernel
def pointBounds16931 : List (Nat × Nat × Nat) := [(2223153152,97854198931738,97854577988849),(2223222784,97854608384183,97854987441551)]
theorem point_links_checked16931 : (cuts16931.take 2).map (fun c => (2223112193-1+2*2^9*c.k,97853963433731+c.lower,97854342490695+c.upper)) = pointBounds16931 := by
 decide +kernel
def cuts16932 : List PrefixCut := [⟨48,286378533,286378715⟩,
⟨116,689348662,689349103⟩,
⟨128,765181114,765181603⟩]
theorem checked16932 : checkPrefixCuts (2^48) 2223243265 9 Manual.Count131072.C016932.packed 128 cuts16932 = true := by
 decide +kernel
def pointBounds16932 : List (Nat × Nat × Nat) := [(2223292416,97855017950465,97855397008090),(2223362048,97855420920594,97855799978478)]
theorem point_links_checked16932 : (cuts16932.take 2).map (fun c => (2223243265-1+2*2^9*c.k,97854731571932+c.lower,97855110629375+c.upper)) = pointBounds16932 := by
 decide +kernel
def cuts16933 : List PrefixCut := [⟨56,340797601,340797814⟩,
⟨124,747413722,747414185⟩,
⟨128,772478684,772479162⟩]
theorem checked16933 : checkPrefixCuts (2^48) 2223374337 9 Manual.Count131072.C016933.packed 128 cuts16933 = true := by
 decide +kernel
def pointBounds16933 : List (Nat × Nat × Nat) := [(2223431680,97855837550647,97856216608792),(2223501312,97856244166768,97856623225163)]
theorem point_links_checked16933 : (cuts16933.take 2).map (fun c => (2223374337-1+2*2^9*c.k,97855496753046+c.lower,97855875810978+c.upper)) = pointBounds16933 := by
 decide +kernel
def cuts16934 : List PrefixCut := [⟨64,379513083,379513324⟩,
⟨128,766863201,766863686⟩]
theorem checked16934 : checkPrefixCuts (2^48) 2223505409 9 Manual.Count131072.C016934.packed 128 cuts16934 = true := by
 decide +kernel
def pointBounds16934 : List (Nat × Nat × Nat) := [(2223570944,97856648744813,97857027803464)]
theorem point_links_checked16934 : (cuts16934.take 1).map (fun c => (2223505409-1+2*2^9*c.k,97856269231730+c.lower,97856648290140+c.upper)) = pointBounds16934 := by
 decide +kernel
def cuts16935 : List PrefixCut := [⟨4,25063439,25063454⟩,
⟨72,433160381,433160648⟩,
⟨128,767577630,767578107⟩]
theorem checked16935 : checkPrefixCuts (2^48) 2223636481 9 Manual.Count131072.C016935.packed 128 cuts16935 = true := by
 decide +kernel
def pointBounds16935 : List (Nat × Nat × Nat) := [(2223640576,97857061158370,97857440217280),(2223710208,97857469255312,97857848314474)]
theorem point_links_checked16935 : (cuts16935.take 2).map (fun c => (2223636481-1+2*2^9*c.k,97857036094931+c.lower,97857415153826+c.upper)) = pointBounds16935 := by
 decide +kernel
def cuts16936 : List PrefixCut := [⟨12,73413694,73413741⟩,
⟨80,482371084,482371386⟩,
⟨128,771076413,771076901⟩]
theorem checked16936 : checkPrefixCuts (2^48) 2223767553 9 Manual.Count131072.C016936.packed 128 cuts16936 = true := by
 decide +kernel
def pointBounds16936 : List (Nat × Nat × Nat) := [(2223779840,97857877086255,97858256145674),(2223849472,97858286043645,97858665103319)]
theorem point_links_checked16936 : (cuts16936.take 2).map (fun c => (2223767553-1+2*2^9*c.k,97857803672561+c.lower,97858182731933+c.upper)) = pointBounds16936 := by
 decide +kernel
def cuts16937 : List PrefixCut := [⟨20,118847015,118847091⟩,
⟨88,524488153,524488489⟩,
⟨128,761032391,761032873⟩]
theorem checked16937 : checkPrefixCuts (2^48) 2223898625 9 Manual.Count131072.C016937.packed 128 cuts16937 = true := by
 decide +kernel
def pointBounds16937 : List (Nat × Nat × Nat) := [(2223919104,97858693595989,97859072655925),(2223988736,97859099237127,97859478297323)]
theorem point_links_checked16937 : (cuts16937.take 2).map (fun c => (2223898625-1+2*2^9*c.k,97858574748974+c.lower,97858953808834+c.upper)) = pointBounds16937 := by
 decide +kernel
def cuts16938 : List PrefixCut := [⟨28,169084102,169084209⟩,
⟨96,580648060,580648420⟩,
⟨128,772883917,772884398⟩]
theorem checked16938 : checkPrefixCuts (2^48) 2224029697 9 Manual.Count131072.C016938.packed 128 cuts16938 = true := by
 decide +kernel
def pointBounds16938 : List (Nat × Nat × Nat) := [(2224058368,97859504865467,97859883925916),(2224128000,97859916429425,97860295490127)]
theorem point_links_checked16938 : (cuts16938.take 2).map (fun c => (2224029697-1+2*2^9*c.k,97859335781365+c.lower,97859714841707+c.upper)) = pointBounds16938 := by
 decide +kernel
def cuts16939 : List PrefixCut := [⟨36,214126433,214126568⟩,
⟨104,622500818,622501210⟩,
⟨128,769041726,769042206⟩]
theorem checked16939 : checkPrefixCuts (2^48) 2224160769 9 Manual.Count131072.C016939.packed 128 cuts16939 = true := by
 decide +kernel
def pointBounds16939 : List (Nat × Nat × Nat) := [(2224197632,97860322791715,97860701852673),(2224267264,97860731166100,97861110227315)]
theorem point_links_checked16939 : (cuts16939.take 2).map (fun c => (2224160769-1+2*2^9*c.k,97860108665282+c.lower,97860487726105+c.upper)) = pointBounds16939 := by
 decide +kernel
def cuts16940 : List PrefixCut := [⟨44,267768302,267768471⟩,
⟨112,678015216,678015643⟩,
⟨128,774184746,774185233⟩]
theorem checked16940 : checkPrefixCuts (2^48) 2224291841 9 Manual.Count131072.C016940.packed 128 cuts16940 = true := by
 decide +kernel
def pointBounds16940 : List (Nat × Nat × Nat) := [(2224336896,97861145475310,97861524536782),(2224406528,97861555722224,97861934783954)]
theorem point_links_checked16940 : (cuts16940.take 2).map (fun c => (2224291841-1+2*2^9*c.k,97860877707008+c.lower,97861256768311+c.upper)) = pointBounds16940 := by
 decide +kernel
def cuts16941 : List PrefixCut := [⟨52,315582984,315583182⟩,
⟨120,726942932,726943390⟩,
⟨128,773253337,773253825⟩]
theorem checked16941 : checkPrefixCuts (2^48) 2224422913 9 Manual.Count131072.C016941.packed 128 cuts16941 = true := by
 decide +kernel
def pointBounds16941 : List (Nat × Nat × Nat) := [(2224476160,97861967474738,97862346536726),(2224545792,97862378834686,97862757896934)]
theorem point_links_checked16941 : (cuts16941.take 2).map (fun c => (2224422913-1+2*2^9*c.k,97861651891754+c.lower,97862030953544+c.upper)) = pointBounds16941 := by
 decide +kernel
def cuts16942 : List PrefixCut := [⟨60,354155123,354155350⟩,
⟨128,756253009,756253491⟩]
theorem checked16942 : checkPrefixCuts (2^48) 2224553985 9 Manual.Count131072.C016942.packed 128 cuts16942 = true := by
 decide +kernel
def pointBounds16942 : List (Nat × Nat × Nat) := [(2224615424,97862779300214,97863158362719),(2224685056,97863181398100,97863560460860)]
theorem point_links_checked16942 : (cuts16942.take 2).map (fun c => (2224553985-1+2*2^9*c.k,97862425145091+c.lower,97862804207369+c.upper)) = pointBounds16942 := by
 decide +kernel
def cuts16943 : List PrefixCut := [⟨68,411194849,411195106⟩,
⟨128,771011358,771011842⟩]
theorem checked16943 : checkPrefixCuts (2^48) 2224685057 9 Manual.Count131072.C016943.packed 128 cuts16943 = true := by
 decide +kernel
def pointBounds16943 : List (Nat × Nat × Nat) := [(2224754688,97863592592949,97863971655966)]
theorem point_links_checked16943 : (cuts16943.take 1).map (fun c => (2224685057-1+2*2^9*c.k,97863181398100+c.lower,97863560460860+c.upper)) = pointBounds16943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000216
