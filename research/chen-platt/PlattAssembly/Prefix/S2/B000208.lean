import PlattAssemblyKernel
import PlattCertificates.Count131072.C016656
import PlattCertificates.Count131072.C016657
import PlattCertificates.Count131072.C016658
import PlattCertificates.Count131072.C016659
import PlattCertificates.Count131072.C016660
import PlattCertificates.Count131072.C016661
import PlattCertificates.Count131072.C016662
import PlattCertificates.Count131072.C016663
import PlattCertificates.Count131072.C016664
import PlattCertificates.Count131072.C016665
import PlattCertificates.Count131072.C016666
import PlattCertificates.Count131072.C016667
import PlattCertificates.Count131072.C016668
import PlattCertificates.Count131072.C016669
import PlattCertificates.Count131072.C016670
import PlattCertificates.Count131072.C016671
import PlattCertificates.Count131072.C016672
import PlattCertificates.Count131072.C016673
import PlattCertificates.Count131072.C016674
import PlattCertificates.Count131072.C016675
import PlattCertificates.Count131072.C016676
import PlattCertificates.Count131072.C016677
import PlattCertificates.Count131072.C016678
import PlattCertificates.Count131072.C016679
import PlattCertificates.Count131072.C016680
import PlattCertificates.Count131072.C016681
import PlattCertificates.Count131072.C016682
import PlattCertificates.Count131072.C016683
import PlattCertificates.Count131072.C016684
import PlattCertificates.Count131072.C016685
import PlattCertificates.Count131072.C016686
import PlattCertificates.Count131072.C016687
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000208
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16656 : List PrefixCut := [⟨3,18532741,18532752⟩,
⟨70,439502235,439502509⟩,
⟨128,796498639,796499142⟩]
theorem checked16656 : checkPrefixCuts (2^48) 2187067393 9 Manual.Count131072.C016656.packed 128 cuts16656 = true := by
 decide +kernel
def pointBounds16656 : List (Nat × Nat × Nat) := [(2187070464,97640161403638,97640540326210),(2187139072,97640582373132,97640961295967)]
theorem point_links_checked16656 : (cuts16656.take 2).map (fun c => (2187067393-1+2*2^9*c.k,97640142870897+c.lower,97640521793458+c.upper)) = pointBounds16656 := by
 decide +kernel
def cuts16657 : List PrefixCut := [⟨9,52377518,52377552⟩,
⟨76,458392613,458392905⟩,
⟨128,781522695,781523194⟩]
theorem checked16657 : checkPrefixCuts (2^48) 2187198465 9 Manual.Count131072.C016657.packed 128 cuts16657 = true := by
 decide +kernel
def pointBounds16657 : List (Nat × Nat × Nat) := [(2187207680,97640991747054,97641370670152),(2187276288,97641397762149,97641776685505)]
theorem point_links_checked16657 : (cuts16657.take 2).map (fun c => (2187198465-1+2*2^9*c.k,97640939369536+c.lower,97641318292600+c.upper)) = pointBounds16657 := by
 decide +kernel
def cuts16658 : List PrefixCut := [⟨15,92781031,92781090⟩,
⟨82,501987754,501988078⟩,
⟨128,788296215,788296721⟩]
theorem checked16658 : checkPrefixCuts (2^48) 2187329537 9 Manual.Count131072.C016658.packed 128 cuts16658 = true := by
 decide +kernel
def pointBounds16658 : List (Nat × Nat × Nat) := [(2187344896,97641813673262,97642192596884),(2187413504,97642222879985,97642601803872)]
theorem point_links_checked16658 : (cuts16658.take 2).map (fun c => (2187329537-1+2*2^9*c.k,97641720892231+c.lower,97642099815794+c.upper)) = pointBounds16658 := by
 decide +kernel
def cuts16659 : List PrefixCut := [⟨21,122756834,122756908⟩,
⟨88,530007666,530007994⟩,
⟨128,774995430,774995913⟩]
theorem checked16659 : checkPrefixCuts (2^48) 2187460609 9 Manual.Count131072.C016659.packed 128 cuts16659 = true := by
 decide +kernel
def pointBounds16659 : List (Nat × Nat × Nat) := [(2187482112,97642631945280,97643010869423),(2187550720,97643039196112,97643418120509)]
theorem point_links_checked16659 : (cuts16659.take 2).map (fun c => (2187460609-1+2*2^9*c.k,97642509188446+c.lower,97642888112515+c.upper)) = pointBounds16659 := by
 decide +kernel
def cuts16660 : List PrefixCut := [⟨27,166753754,166753863⟩,
⟨94,583629048,583629416⟩,
⟨128,790003142,790003643⟩]
theorem checked16660 : checkPrefixCuts (2^48) 2187591681 9 Manual.Count131072.C016660.packed 128 cuts16660 = true := by
 decide +kernel
def pointBounds16660 : List (Nat × Nat × Nat) := [(2187619328,97643450937630,97643829862291),(2187687936,97643867812924,97644246737844)]
theorem point_links_checked16660 : (cuts16660.take 2).map (fun c => (2187591681-1+2*2^9*c.k,97643284183876+c.lower,97643663108428+c.upper)) = pointBounds16660 := by
 decide +kernel
def cuts16661 : List PrefixCut := [⟨33,199165882,199166012⟩,
⟨100,606751692,606752073⟩,
⟨128,780820924,780821415⟩]
theorem checked16661 : checkPrefixCuts (2^48) 2187722753 9 Manual.Count131072.C016661.packed 128 cuts16661 = true := by
 decide +kernel
def pointBounds16661 : List (Nat × Nat × Nat) := [(2187756544,97644273352900,97644652278083),(2187825152,97644680938710,97645059864144)]
theorem point_links_checked16661 : (cuts16661.take 2).map (fun c => (2187722753-1+2*2^9*c.k,97644074187018+c.lower,97644453112071+c.upper)) = pointBounds16661 := by
 decide +kernel
def cuts16662 : List PrefixCut := [⟨39,236591472,236591623⟩,
⟨106,649940873,649941276⟩,
⟨128,783604466,783604951⟩]
theorem checked16662 : checkPrefixCuts (2^48) 2187853825 9 Manual.Count131072.C016662.packed 128 cuts16662 = true := by
 decide +kernel
def pointBounds16662 : List (Nat × Nat × Nat) := [(2187893760,97645091599414,97645470525109),(2187962368,97645504948815,97645883874762)]
theorem point_links_checked16662 : (cuts16662.take 2).map (fun c => (2187853825-1+2*2^9*c.k,97644855007942+c.lower,97645233933486+c.upper)) = pointBounds16662 := by
 decide +kernel
def cuts16663 : List PrefixCut := [⟨45,269381314,269381482⟩,
⟨112,682576186,682576616⟩,
⟨128,777640033,777640521⟩]
theorem checked16663 : checkPrefixCuts (2^48) 2187984897 9 Manual.Count131072.C016663.packed 128 cuts16663 = true := by
 decide +kernel
def pointBounds16663 : List (Nat × Nat × Nat) := [(2188030976,97645907993722,97646286919919),(2188099584,97646321188594,97646700115053)]
theorem point_links_checked16663 : (cuts16663.take 2).map (fun c => (2187984897-1+2*2^9*c.k,97645638612408+c.lower,97646017538437+c.upper)) = pointBounds16663 := by
 decide +kernel
def cuts16664 : List PrefixCut := [⟨51,311171654,311171849⟩,
⟨118,723440169,723440618⟩,
⟨128,785182862,785183350⟩]
theorem checked16664 : checkPrefixCuts (2^48) 2188115969 9 Manual.Count131072.C016664.packed 128 cuts16664 = true := by
 decide +kernel
def pointBounds16664 : List (Nat × Nat × Nat) := [(2188168192,97646727424095,97647106350807),(2188236800,97647139692610,97647518619576)]
theorem point_links_checked16664 : (cuts16664.take 2).map (fun c => (2188115969-1+2*2^9*c.k,97646416252441+c.lower,97646795178958+c.upper)) = pointBounds16664 := by
 decide +kernel
def cuts16665 : List PrefixCut := [⟨57,342537936,342538159⟩,
⟨124,756324141,756324629⟩,
⟨128,781534194,781534698⟩]
theorem checked16665 : checkPrefixCuts (2^48) 2188247041 9 Manual.Count131072.C016665.packed 128 cuts16665 = true := by
 decide +kernel
def pointBounds16665 : List (Nat × Nat × Nat) := [(2188305408,97647543973239,97647922900467),(2188374016,97647957759444,97648336686937)]
theorem point_links_checked16665 : (cuts16665.take 2).map (fun c => (2188247041-1+2*2^9*c.k,97647201435303+c.lower,97647580362308+c.upper)) = pointBounds16665 := by
 decide +kernel
def cuts16666 : List PrefixCut := [⟨63,392550481,392550726⟩,
⟨128,796535970,796536476⟩]
theorem checked16666 : checkPrefixCuts (2^48) 2188378113 9 Manual.Count131072.C016666.packed 128 cuts16666 = true := by
 decide +kernel
def pointBounds16666 : List (Nat × Nat × Nat) := [(2188442624,97648375519978,97648754447732)]
theorem point_links_checked16666 : (cuts16666.take 1).map (fun c => (2188378113-1+2*2^9*c.k,97647982969497+c.lower,97648361897006+c.upper)) = pointBounds16666 := by
 decide +kernel
def cuts16667 : List PrefixCut := [⟨2,10932262,10932269⟩,
⟨69,418506153,418506415⟩,
⟨128,787356749,787357245⟩]
theorem checked16667 : checkPrefixCuts (2^48) 2188509185 9 Manual.Count131072.C016667.packed 128 cuts16667 = true := by
 decide +kernel
def pointBounds16667 : List (Nat × Nat × Nat) := [(2188511232,97648790437729,97649169365751),(2188579840,97649198011620,97649576939897)]
theorem point_links_checked16667 : (cuts16667.take 2).map (fun c => (2188509185-1+2*2^9*c.k,97648779505467+c.lower,97649158433482+c.upper)) = pointBounds16667 := by
 decide +kernel
def cuts16668 : List PrefixCut := [⟨8,46427114,46427143⟩,
⟨75,459891293,459891584⟩,
⟨128,783966061,783966556⟩]
theorem checked16668 : checkPrefixCuts (2^48) 2188640257 9 Manual.Count131072.C016668.packed 128 cuts16668 = true := by
 decide +kernel
def pointBounds16668 : List (Nat × Nat × Nat) := [(2188648448,97649613289330,97649992217870),(2188717056,97650026753509,97650405682311)]
theorem point_links_checked16668 : (cuts16668.take 2).map (fun c => (2188640257-1+2*2^9*c.k,97649566862216+c.lower,97649945790727+c.upper)) = pointBounds16668 := by
 decide +kernel
def cuts16669 : List PrefixCut := [⟨14,87318766,87318822⟩,
⟨81,497156363,497156676⟩,
⟨128,778518296,778518792⟩]
theorem checked16669 : checkPrefixCuts (2^48) 2188771329 9 Manual.Count131072.C016669.packed 128 cuts16669 = true := by
 decide +kernel
def pointBounds16669 : List (Nat × Nat × Nat) := [(2188785664,97650438147043,97650817076105),(2188854272,97650847984640,97651226913959)]
theorem point_links_checked16669 : (cuts16669.take 2).map (fun c => (2188771329-1+2*2^9*c.k,97650350828277+c.lower,97650729757283+c.upper)) = pointBounds16669 := by
 decide +kernel
def cuts16670 : List PrefixCut := [⟨20,122418830,122418910⟩,
⟨87,534545264,534545599⟩,
⟨128,786572507,786572998⟩]
theorem checked16670 : checkPrefixCuts (2^48) 2188902401 9 Manual.Count131072.C016670.packed 128 cuts16670 = true := by
 decide +kernel
def pointBounds16670 : List (Nat × Nat × Nat) := [(2188922880,97651251765403,97651630694985),(2188991488,97651663891837,97652042821674)]
theorem point_links_checked16670 : (cuts16670.take 2).map (fun c => (2188902401-1+2*2^9*c.k,97651129346573+c.lower,97651508276075+c.upper)) = pointBounds16670 := by
 decide +kernel
def cuts16671 : List PrefixCut := [⟨26,158414641,158414738⟩,
⟨93,568972258,568972615⟩,
⟨128,777910640,777911128⟩]
theorem checked16671 : checkPrefixCuts (2^48) 2189033473 9 Manual.Count131072.C016671.packed 128 cuts16671 = true := by
 decide +kernel
def pointBounds16671 : List (Nat × Nat × Nat) := [(2189060096,97652074333721,97652453263811),(2189128704,97652484891338,97652863821688)]
theorem point_links_checked16671 : (cuts16671.take 2).map (fun c => (2189033473-1+2*2^9*c.k,97651915919080+c.lower,97652294849073+c.upper)) = pointBounds16671 := by
 decide +kernel
def cuts16672 : List PrefixCut := [⟨32,193120290,193120412⟩,
⟨99,599023544,599023922⟩,
⟨128,776578128,776578617⟩]
theorem checked16672 : checkPrefixCuts (2^48) 2189164545 9 Manual.Count131072.C016672.packed 128 cuts16672 = true := by
 decide +kernel
def pointBounds16672 : List (Nat × Nat × Nat) := [(2189197312,97652886950010,97653265880613),(2189265920,97653292853264,97653671784123)]
theorem point_links_checked16672 : (cuts16672.take 2).map (fun c => (2189164545-1+2*2^9*c.k,97652693829720+c.lower,97653072760201+c.upper)) = pointBounds16672 := by
 decide +kernel
def cuts16673 : List PrefixCut := [⟨38,232835863,232836011⟩,
⟨105,642699212,642699625⟩,
⟨128,780131663,780132163⟩]
theorem checked16673 : checkPrefixCuts (2^48) 2189295617 9 Manual.Count131072.C016673.packed 128 cuts16673 = true := by
 decide +kernel
def pointBounds16673 : List (Nat × Nat × Nat) := [(2189334528,97653703243711,97654082174829),(2189403136,97654113107060,97654492038443)]
theorem point_links_checked16673 : (cuts16673.take 2).map (fun c => (2189295617-1+2*2^9*c.k,97653470407848+c.lower,97653849338818+c.upper)) = pointBounds16673 := by
 decide +kernel
def cuts16674 : List PrefixCut := [⟨44,266889879,266890050⟩,
⟨111,680584199,680584634⟩,
⟨128,785741220,785741722⟩]
theorem checked16674 : checkPrefixCuts (2^48) 2189426689 9 Manual.Count131072.C016674.packed 128 cuts16674 = true := by
 decide +kernel
def pointBounds16674 : List (Nat × Nat × Nat) := [(2189471744,97654517429390,97654896361031),(2189540352,97654931123710,97655310055615)]
theorem point_links_checked16674 : (cuts16674.take 2).map (fun c => (2189426689-1+2*2^9*c.k,97654250539511+c.lower,97654629470981+c.upper)) = pointBounds16674 := by
 decide +kernel
def cuts16675 : List PrefixCut := [⟨50,304024980,304025170⟩,
⟨117,715636575,715637019⟩,
⟨128,787365211,787365700⟩]
theorem checked16675 : checkPrefixCuts (2^48) 2189557761 9 Manual.Count131072.C016675.packed 128 cuts16675 = true := by
 decide +kernel
def pointBounds16675 : List (Nat × Nat × Nat) := [(2189608960,97655340305711,97655719237873),(2189677568,97655751917306,97656130849722)]
theorem point_links_checked16675 : (cuts16675.take 2).map (fun c => (2189557761-1+2*2^9*c.k,97655036280731+c.lower,97655415212703+c.upper)) = pointBounds16675 := by
 decide +kernel
def cuts16676 : List PrefixCut := [⟨56,336528011,336528222⟩,
⟨123,748499469,748499944⟩,
⟨128,780119836,780120331⟩]
theorem checked16676 : checkPrefixCuts (2^48) 2189688833 9 Manual.Count131072.C016676.packed 128 cuts16676 = true := by
 decide +kernel
def pointBounds16676 : List (Nat × Nat × Nat) := [(2189746176,97656160173953,97656539106625),(2189814784,97656572145411,97656951078347)]
theorem point_links_checked16676 : (cuts16676.take 2).map (fun c => (2189688833-1+2*2^9*c.k,97655823645942+c.lower,97656202578403+c.upper)) = pointBounds16676 := by
 decide +kernel
def cuts16677 : List PrefixCut := [⟨62,379566901,379567144⟩,
⟨128,783543642,783544141⟩]
theorem checked16677 : checkPrefixCuts (2^48) 2189819905 9 Manual.Count131072.C016677.packed 128 cuts16677 = true := by
 decide +kernel
def pointBounds16677 : List (Nat × Nat × Nat) := [(2189883392,97656983332679,97657362265878)]
theorem point_links_checked16677 : (cuts16677.take 1).map (fun c => (2189819905-1+2*2^9*c.k,97656603765778+c.lower,97656982698734+c.upper)) = pointBounds16677 := by
 decide +kernel
def cuts16678 : List PrefixCut := [⟨1,6426510,6426514⟩,
⟨68,416559860,416560125⟩,
⟨128,785938768,785939267⟩]
theorem checked16678 : checkPrefixCuts (2^48) 2189950977 9 Manual.Count131072.C016678.packed 128 cuts16678 = true := by
 decide +kernel
def pointBounds16678 : List (Nat × Nat × Nat) := [(2189952000,97657393735930,97657772669389),(2190020608,97657803869280,97658182803000)]
theorem point_links_checked16678 : (cuts16678.take 2).map (fun c => (2189950977-1+2*2^9*c.k,97657387309420+c.lower,97657766242875+c.upper)) = pointBounds16678 := by
 decide +kernel
def cuts16679 : List PrefixCut := [⟨7,42155321,42155347⟩,
⟨74,453933727,453934016⟩,
⟨128,783064357,783064851⟩]
theorem checked16679 : checkPrefixCuts (2^48) 2190082049 9 Manual.Count131072.C016679.packed 128 cuts16679 = true := by
 decide +kernel
def pointBounds16679 : List (Nat × Nat × Nat) := [(2190089216,97658215403509,97658594337489),(2190157824,97658627181915,97659006116158)]
theorem point_links_checked16679 : (cuts16679.take 2).map (fun c => (2190082049-1+2*2^9*c.k,97658173248188+c.lower,97658552182142+c.upper)) = pointBounds16679 := by
 decide +kernel
def cuts16680 : List PrefixCut := [⟨13,79421933,79421982⟩,
⟨80,486548224,486548528⟩,
⟨128,781089880,781090371⟩]
theorem checked16680 : checkPrefixCuts (2^48) 2190213121 9 Manual.Count131072.C016680.packed 128 cuts16680 = true := by
 decide +kernel
def pointBounds16680 : List (Nat × Nat × Nat) := [(2190226432,97659035734478,97659414668975),(2190295040,97659442860769,97659821795521)]
theorem point_links_checked16680 : (cuts16680.take 2).map (fun c => (2190213121-1+2*2^9*c.k,97658956312545+c.lower,97659335246993+c.upper)) = pointBounds16680 := by
 decide +kernel
def cuts16681 : List PrefixCut := [⟨19,112314745,112314815⟩,
⟨86,516202684,516203010⟩,
⟨128,776288175,776288662⟩]
theorem checked16681 : checkPrefixCuts (2^48) 2190344193 9 Manual.Count131072.C016681.packed 128 cuts16681 = true := by
 decide +kernel
def pointBounds16681 : List (Nat × Nat × Nat) := [(2190363648,97659849717170,97660228652179),(2190432256,97660253605109,97660632540374)]
theorem point_links_checked16681 : (cuts16681.take 2).map (fun c => (2190344193-1+2*2^9*c.k,97659737402425+c.lower,97660116337364+c.upper)) = pointBounds16681 := by
 decide +kernel
def cuts16682 : List PrefixCut := [⟨25,152013983,152014083⟩,
⟨92,559474653,559475005⟩,
⟨128,776113644,776114132⟩]
theorem checked16682 : checkPrefixCuts (2^48) 2190475265 9 Manual.Count131072.C016682.packed 128 cuts16682 = true := by
 decide +kernel
def pointBounds16682 : List (Nat × Nat × Nat) := [(2190500864,97660665704583,97661044640109),(2190569472,97661073165253,97661452101031)]
theorem point_links_checked16682 : (cuts16682.take 2).map (fun c => (2190475265-1+2*2^9*c.k,97660513690600+c.lower,97660892626026+c.upper)) = pointBounds16682 := by
 decide +kernel
def cuts16683 : List PrefixCut := [⟨31,193892649,193892771⟩,
⟨98,601970215,601970594⟩,
⟨128,787631024,787631517⟩]
theorem checked16683 : checkPrefixCuts (2^48) 2190606337 9 Manual.Count131072.C016683.packed 128 cuts16683 = true := by
 decide +kernel
def pointBounds16683 : List (Nat × Nat × Nat) := [(2190638080,97661483696893,97661862632929),(2190706688,97661891774459,97662270710752)]
theorem point_links_checked16683 : (cuts16683.take 2).map (fun c => (2190606337-1+2*2^9*c.k,97661289804244+c.lower,97661668740158+c.upper)) = pointBounds16683 := by
 decide +kernel
def cuts16684 : List PrefixCut := [⟨37,231526320,231526465⟩,
⟨104,638935857,638936257⟩,
⟨128,786427565,786428060⟩]
theorem checked16684 : checkPrefixCuts (2^48) 2190737409 9 Manual.Count131072.C016684.packed 128 cuts16684 = true := by
 decide +kernel
def pointBounds16684 : List (Nat × Nat × Nat) := [(2190775296,97662308961588,97662687898140),(2190843904,97662716371125,97663095307932)]
theorem point_links_checked16684 : (cuts16684.take 2).map (fun c => (2190737409-1+2*2^9*c.k,97662077435268+c.lower,97662456371675+c.upper)) = pointBounds16684 := by
 decide +kernel
def cuts16685 : List PrefixCut := [⟨43,261960749,261960916⟩,
⟨110,667803243,667803668⟩,
⟨128,779956897,779957393⟩]
theorem checked16685 : checkPrefixCuts (2^48) 2190868481 9 Manual.Count131072.C016685.packed 128 cuts16685 = true := by
 decide +kernel
def pointBounds16685 : List (Nat × Nat × Nat) := [(2190912512,97663125823582,97663504760651),(2190981120,97663531666076,97663910603403)]
theorem point_links_checked16685 : (cuts16685.take 2).map (fun c => (2190868481-1+2*2^9*c.k,97662863862833+c.lower,97663242799735+c.upper)) = pointBounds16685 := by
 decide +kernel
def cuts16686 : List PrefixCut := [⟨49,308192914,308193109⟩,
⟨116,714266898,714267349⟩,
⟨128,786590659,786591157⟩]
theorem checked16686 : checkPrefixCuts (2^48) 2190999553 9 Manual.Count131072.C016686.packed 128 cuts16686 = true := by
 decide +kernel
def pointBounds16686 : List (Nat × Nat × Nat) := [(2191049728,97663952012644,97664330950237),(2191118336,97664358086628,97664737024477)]
theorem point_links_checked16686 : (cuts16686.take 2).map (fun c => (2190999553-1+2*2^9*c.k,97663643819730+c.lower,97664022757128+c.upper)) = pointBounds16686 := by
 decide +kernel
def cuts16687 : List PrefixCut := [⟨55,343757300,343757512⟩,
⟨122,750705018,750705489⟩,
⟨128,786158192,786158686⟩]
theorem checked16687 : checkPrefixCuts (2^48) 2191130625 9 Manual.Count131072.C016687.packed 128 cuts16687 = true := by
 decide +kernel
def pointBounds16687 : List (Nat × Nat × Nat) := [(2191186944,97664774167689,97665153105797),(2191255552,97665181115407,97665560053774)]
theorem point_links_checked16687 : (cuts16687.take 2).map (fun c => (2191130625-1+2*2^9*c.k,97664430410389+c.lower,97664809348285+c.upper)) = pointBounds16687 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000208
