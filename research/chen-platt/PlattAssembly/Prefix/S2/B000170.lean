import PlattAssemblyKernel
import PlattCertificates.Count131072.C015440
import PlattCertificates.Count131072.C015441
import PlattCertificates.Count131072.C015442
import PlattCertificates.Count131072.C015443
import PlattCertificates.Count131072.C015444
import PlattCertificates.Count131072.C015445
import PlattCertificates.Count131072.C015446
import PlattCertificates.Count131072.C015447
import PlattCertificates.Count131072.C015448
import PlattCertificates.Count131072.C015449
import PlattCertificates.Count131072.C015450
import PlattCertificates.Count131072.C015451
import PlattCertificates.Count131072.C015452
import PlattCertificates.Count131072.C015453
import PlattCertificates.Count131072.C015454
import PlattCertificates.Count131072.C015455
import PlattCertificates.Count131072.C015456
import PlattCertificates.Count131072.C015457
import PlattCertificates.Count131072.C015458
import PlattCertificates.Count131072.C015459
import PlattCertificates.Count131072.C015460
import PlattCertificates.Count131072.C015461
import PlattCertificates.Count131072.C015462
import PlattCertificates.Count131072.C015463
import PlattCertificates.Count131072.C015464
import PlattCertificates.Count131072.C015465
import PlattCertificates.Count131072.C015466
import PlattCertificates.Count131072.C015467
import PlattCertificates.Count131072.C015468
import PlattCertificates.Count131072.C015469
import PlattCertificates.Count131072.C015470
import PlattCertificates.Count131072.C015471
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15440 : List PrefixCut := [⟨30,197533623,197533758⟩,
⟨92,613691091,613691501⟩,
⟨128,854939838,854940403⟩]
theorem checked15440 : checkPrefixCuts (2^48) 2027683841 9 Manual.Count131072.C015440.packed 128 cuts15440 = true := by
 decide +kernel
def pointBounds15440 : List (Nat × Nat × Nat) := [(2027714560,96648306822883,96648685107677),(2027778048,96648722980351,96649101265420)]
theorem point_links_checked15440 : (cuts15440.take 2).map (fun c => (2027683841-1+2*2^9*c.k,96648109289260+c.lower,96648487573919+c.upper)) = pointBounds15440 := by
 decide +kernel
def cuts15441 : List PrefixCut := [⟨26,172674776,172674891⟩,
⟨88,579367494,579367878⟩,
⟨128,840032822,840033377⟩]
theorem checked15441 : checkPrefixCuts (2^48) 2027814913 9 Manual.Count131072.C015441.packed 128 cuts15441 = true := by
 decide +kernel
def pointBounds15441 : List (Nat × Nat × Nat) := [(2027841536,96649136903874,96649515189213),(2027905024,96649543596592,96649921882200)]
theorem point_links_checked15441 : (cuts15441.take 2).map (fun c => (2027814913-1+2*2^9*c.k,96648964229098+c.lower,96649342514322+c.upper)) = pointBounds15441 := by
 decide +kernel
def cuts15442 : List PrefixCut := [⟨22,141711989,141712085⟩,
⟨84,547685351,547685716⟩,
⟨128,838174043,838174595⟩]
theorem checked15442 : checkPrefixCuts (2^48) 2027945985 9 Manual.Count131072.C015442.packed 128 cuts15442 = true := by
 decide +kernel
def pointBounds15442 : List (Nat × Nat × Nat) := [(2027968512,96649945973909,96650324259784),(2028032000,96650351947271,96650730233415)]
theorem point_links_checked15442 : (cuts15442.take 2).map (fun c => (2027945985-1+2*2^9*c.k,96649804261920+c.lower,96650182547699+c.upper)) = pointBounds15442 := by
 decide +kernel
def cuts15443 : List PrefixCut := [⟨18,115888323,115888399⟩,
⟨80,530024547,530024894⟩,
⟨128,851443085,851443641⟩]
theorem checked15443 : checkPrefixCuts (2^48) 2028077057 9 Manual.Count131072.C015443.packed 128 cuts15443 = true := by
 decide +kernel
def pointBounds15443 : List (Nat × Nat × Nat) := [(2028095488,96650758324286,96651136610693),(2028158976,96651172460510,96651550747188)]
theorem point_links_checked15443 : (cuts15443.take 2).map (fun c => (2028077057-1+2*2^9*c.k,96650642435963+c.lower,96651020722294+c.upper)) = pointBounds15443 := by
 decide +kernel
def cuts15444 : List PrefixCut := [⟨14,92427210,92427272⟩,
⟨76,501541669,501541999⟩,
⟨128,857077919,857078483⟩]
theorem checked15444 : checkPrefixCuts (2^48) 2028208129 9 Manual.Count131072.C015444.packed 128 cuts15444 = true := by
 decide +kernel
def pointBounds15444 : List (Nat × Nat × Nat) := [(2028222464,96651586306258,96651964593207),(2028285952,96651995420717,96652373707934)]
theorem point_links_checked15444 : (cuts15444.take 2).map (fun c => (2028208129-1+2*2^9*c.k,96651493879048+c.lower,96651872165935+c.upper)) = pointBounds15444 := by
 decide +kernel
def cuts15445 : List PrefixCut := [⟨10,64944720,64944763⟩,
⟨72,467233763,467234077⟩,
⟨128,838011368,838011932⟩]
theorem checked15445 : checkPrefixCuts (2^48) 2028339201 9 Manual.Count131072.C015445.packed 128 cuts15445 = true := by
 decide +kernel
def pointBounds15445 : List (Nat × Nat × Nat) := [(2028349440,96652415901687,96652794189181),(2028412928,96652818190730,96653196478495)]
theorem point_links_checked15445 : (cuts15445.take 2).map (fun c => (2028339201-1+2*2^9*c.k,96652350956967+c.lower,96652729244418+c.upper)) = pointBounds15445 := by
 decide +kernel
def cuts15446 : List PrefixCut := [⟨6,41073532,41073558⟩,
⟨68,446251452,446251743⟩,
⟨128,849196761,849197320⟩]
theorem checked15446 : checkPrefixCuts (2^48) 2028470273 9 Manual.Count131072.C015446.packed 128 cuts15446 = true := by
 decide +kernel
def pointBounds15446 : List (Nat × Nat × Nat) := [(2028476416,96653230041867,96653608329908),(2028539904,96653635219787,96654013508093)]
theorem point_links_checked15446 : (cuts15446.take 2).map (fun c => (2028470273-1+2*2^9*c.k,96653188968335+c.lower,96653567256350+c.upper)) = pointBounds15446 := by
 decide +kernel
def cuts15447 : List PrefixCut := [⟨2,13320298,13320308⟩,
⟨64,419721571,419721849⟩,
⟨126,818479137,818479677⟩,
⟨128,833879753,833880303⟩]
theorem checked15447 : checkPrefixCuts (2^48) 2028601345 9 Manual.Count131072.C015447.packed 128 cuts15447 = true := by
 decide +kernel
def pointBounds15447 : List (Nat × Nat × Nat) := [(2028603392,96654051485394,96654429773978),(2028666880,96654457886667,96654836175519),(2028730368,96654856644233,96655234933347)]
theorem point_links_checked15447 : (cuts15447.take 3).map (fun c => (2028601345-1+2*2^9*c.k,96654038165096+c.lower,96654416453670+c.upper)) = pointBounds15447 := by
 decide +kernel
def cuts15448 : List PrefixCut := [⟨60,404294499,404294766⟩,
⟨122,816623382,816623915⟩,
⟨128,857966547,857967107⟩]
theorem checked15448 : checkPrefixCuts (2^48) 2028732417 9 Manual.Count131072.C015448.packed 128 cuts15448 = true := by
 decide +kernel
def pointBounds15448 : List (Nat × Nat × Nat) := [(2028793856,96655276339348,96655654628739),(2028857344,96655688668231,96656066957888)]
theorem point_links_checked15448 : (cuts15448.take 2).map (fun c => (2028732417-1+2*2^9*c.k,96654872044849+c.lower,96655250333973+c.upper)) = pointBounds15448 := by
 decide +kernel
def cuts15449 : List PrefixCut := [⟨56,361261510,361261744⟩,
⟨118,776477970,776478478⟩,
⟨128,842373129,842373681⟩]
theorem checked15449 : checkPrefixCuts (2^48) 2028863489 9 Manual.Count131072.C015449.packed 128 cuts15449 = true := by
 decide +kernel
def pointBounds15449 : List (Nat × Nat × Nat) := [(2028920832,96656091272906,96656469562824),(2028984320,96656506489366,96656884779558)]
theorem point_links_checked15449 : (cuts15449.take 2).map (fun c => (2028863489-1+2*2^9*c.k,96655730011396+c.lower,96656108301080+c.upper)) = pointBounds15449 := by
 decide +kernel
def cuts15450 : List PrefixCut := [⟨52,348059694,348059921⟩,
⟨114,755897931,755898424⟩,
⟨128,849116304,849116856⟩]
theorem checked15450 : checkPrefixCuts (2^48) 2028994561 9 Manual.Count131072.C015450.packed 128 cuts15450 = true := by
 decide +kernel
def pointBounds15450 : List (Nat × Nat × Nat) := [(2029047808,96656920444219,96657298734682),(2029111296,96657328282456,96657706573185)]
theorem point_links_checked15450 : (cuts15450.take 2).map (fun c => (2028994561-1+2*2^9*c.k,96656572384525+c.lower,96656950674761+c.upper)) = pointBounds15450 := by
 decide +kernel
def cuts15451 : List PrefixCut := [⟨48,320849249,320849462⟩,
⟨110,736291126,736291608⟩,
⟨128,853777651,853778210⟩]
theorem checked15451 : checkPrefixCuts (2^48) 2029125633 9 Manual.Count131072.C015451.packed 128 cuts15451 = true := by
 decide +kernel
def pointBounds15451 : List (Nat × Nat × Nat) := [(2029174784,96657742350078,96658120641079),(2029238272,96658157791955,96658536083225)]
theorem point_links_checked15451 : (cuts15451.take 2).map (fun c => (2029125633-1+2*2^9*c.k,96657421500829+c.lower,96657799791617+c.upper)) = pointBounds15451 := by
 decide +kernel
def cuts15452 : List PrefixCut := [⟨44,287400551,287400741⟩,
⟨106,698100455,698100916⟩,
⟨128,838465034,838465587⟩]
theorem checked15452 : checkPrefixCuts (2^48) 2029256705 9 Manual.Count131072.C015452.packed 128 cuts15452 = true := by
 decide +kernel
def pointBounds15452 : List (Nat × Nat × Nat) := [(2029301760,96658562679031,96658940970568),(2029365248,96658973378935,96659351670743)]
theorem point_links_checked15452 : (cuts15452.take 2).map (fun c => (2029256705-1+2*2^9*c.k,96658275278480+c.lower,96658653569827+c.upper)) = pointBounds15452 := by
 decide +kernel
def cuts15453 : List PrefixCut := [⟨40,266022764,266022939⟩,
⟨102,681135199,681135639⟩,
⟨128,852141653,852142206⟩]
theorem checked15453 : checkPrefixCuts (2^48) 2029387777 9 Manual.Count131072.C015453.packed 128 cuts15453 = true := by
 decide +kernel
def pointBounds15453 : List (Nat × Nat × Nat) := [(2029428736,96659379766278,96659758058353),(2029492224,96659794878713,96660173171053)]
theorem point_links_checked15453 : (cuts15453.take 2).map (fun c => (2029387777-1+2*2^9*c.k,96659113743514+c.lower,96659492035414+c.upper)) = pointBounds15453 := by
 decide +kernel
def cuts15454 : List PrefixCut := [⟨36,236881150,236881305⟩,
⟨98,647252351,647252772⟩,
⟨128,850560972,850561523⟩]
theorem checked15454 : checkPrefixCuts (2^48) 2029518849 9 Manual.Count131072.C015454.packed 128 cuts15454 = true := by
 decide +kernel
def pointBounds15454 : List (Nat × Nat × Nat) := [(2029555712,96660202766317,96660581058925),(2029619200,96660613137518,96660991430392)]
theorem point_links_checked15454 : (cuts15454.take 2).map (fun c => (2029518849-1+2*2^9*c.k,96659965885167+c.lower,96660344177620+c.upper)) = pointBounds15454 := by
 decide +kernel
def cuts15455 : List PrefixCut := [⟨32,216618772,216618911⟩,
⟨94,629737736,629738143⟩,
⟨128,850228960,850229510⟩]
theorem checked15455 : checkPrefixCuts (2^48) 2029649921 9 Manual.Count131072.C015455.packed 128 cuts15455 = true := by
 decide +kernel
def pointBounds15455 : List (Nat × Nat × Nat) := [(2029682688,96661033064911,96661411358054),(2029746176,96661446183875,96661824477286)]
theorem point_links_checked15455 : (cuts15455.take 2).map (fun c => (2029649921-1+2*2^9*c.k,96660816446139+c.lower,96661194739143+c.upper)) = pointBounds15455 := by
 decide +kernel
def cuts15456 : List PrefixCut := [⟨28,185403866,185403989⟩,
⟨90,591840945,591841339⟩,
⟨128,842963102,842963663⟩]
theorem checked15456 : checkPrefixCuts (2^48) 2029780993 9 Manual.Count131072.C015456.packed 128 cuts15456 = true := by
 decide +kernel
def pointBounds15456 : List (Nat × Nat × Nat) := [(2029809664,96661852078965,96662230372642),(2029873152,96662258516044,96662636809992)]
theorem point_links_checked15456 : (cuts15456.take 2).map (fun c => (2029780993-1+2*2^9*c.k,96661666675099+c.lower,96662044968653+c.upper)) = pointBounds15456 := by
 decide +kernel
def cuts15457 : List PrefixCut := [⟨24,161403458,161403561⟩,
⟨86,562407444,562407810⟩,
⟨128,841938137,841938695⟩]
theorem checked15457 : checkPrefixCuts (2^48) 2029912065 9 Manual.Count131072.C015457.packed 128 cuts15457 = true := by
 decide +kernel
def pointBounds15457 : List (Nat × Nat × Nat) := [(2029936640,96662671041659,96663049335877),(2030000128,96663072045645,96663450340126)]
theorem point_links_checked15457 : (cuts15457.take 2).map (fun c => (2029912065-1+2*2^9*c.k,96662509638201+c.lower,96662887932316+c.upper)) = pointBounds15457 := by
 decide +kernel
def cuts15458 : List PrefixCut := [⟨20,133385104,133385192⟩,
⟨82,541019194,541019550⟩,
⟨128,846320537,846321092⟩]
theorem checked15458 : checkPrefixCuts (2^48) 2030043137 9 Manual.Count131072.C015458.packed 128 cuts15458 = true := by
 decide +kernel
def pointBounds15458 : List (Nat × Nat × Nat) := [(2030063616,96663484961442,96663863256203),(2030127104,96663892595532,96664270890561)]
theorem point_links_checked15458 : (cuts15458.take 2).map (fun c => (2030043137-1+2*2^9*c.k,96663351576338+c.lower,96663729871011+c.upper)) = pointBounds15458 := by
 decide +kernel
def cuts15459 : List PrefixCut := [⟨16,107588615,107588686⟩,
⟨78,519079230,519079568⟩,
⟨128,847375163,847375718⟩]
theorem checked15459 : checkPrefixCuts (2^48) 2030174209 9 Manual.Count131072.C015459.packed 128 cuts15459 = true := by
 decide +kernel
def pointBounds15459 : List (Nat × Nat × Nat) := [(2030190592,96664305485490,96664683780789),(2030254080,96664716976105,96665095271671)]
theorem point_links_checked15459 : (cuts15459.take 2).map (fun c => (2030174209-1+2*2^9*c.k,96664197896875+c.lower,96664576192103+c.upper)) = pointBounds15459 := by
 decide +kernel
def cuts15460 : List PrefixCut := [⟨12,79577247,79577301⟩,
⟨74,484387765,484388082⟩,
⟨128,845102218,845102766⟩]
theorem checked15460 : checkPrefixCuts (2^48) 2030305281 9 Manual.Count131072.C015460.packed 128 cuts15460 = true := by
 decide +kernel
def pointBounds15460 : List (Nat × Nat × Nat) := [(2030317568,96665124849285,96665503145122),(2030381056,96665529659803,96665907955903)]
theorem point_links_checked15460 : (cuts15460.take 2).map (fun c => (2030305281-1+2*2^9*c.k,96665045272038+c.lower,96665423567821+c.upper)) = pointBounds15460 := by
 decide +kernel
def cuts15461 : List PrefixCut := [⟨8,54341981,54342015⟩,
⟨70,468969535,468969838⟩,
⟨128,854474120,854474675⟩]
theorem checked15461 : checkPrefixCuts (2^48) 2030436353 9 Manual.Count131072.C015461.packed 128 cuts15461 = true := by
 decide +kernel
def pointBounds15461 : List (Nat × Nat × Nat) := [(2030444544,96665944716237,96666323012602),(2030508032,96666359343791,96666737640425)]
theorem point_links_checked15461 : (cuts15461.take 2).map (fun c => (2030436353-1+2*2^9*c.k,96665890374256+c.lower,96666268670587+c.upper)) = pointBounds15461 := by
 decide +kernel
def cuts15462 : List PrefixCut := [⟨4,26476170,26476188⟩,
⟨66,434424188,434424470⟩,
⟨128,841111980,841112527⟩]
theorem checked15462 : checkPrefixCuts (2^48) 2030567425 9 Manual.Count131072.C015462.packed 128 cuts15462 = true := by
 decide +kernel
def pointBounds15462 : List (Nat × Nat × Nat) := [(2030571520,96666771324546,96667149621450),(2030635008,96667179272564,96667557569732),(2030698496,96667585960356,96667964257789)]
theorem point_links_checked15462 : (cuts15462.take 3).map (fun c => (2030567425-1+2*2^9*c.k,96666744848376+c.lower,96667123145262+c.upper)) = pointBounds15462 := by
 decide +kernel
def cuts15463 : List PrefixCut := [⟨62,410140245,410140512⟩,
⟨124,824148507,824149048⟩,
⟨128,849928310,849928868⟩]
theorem checked15463 : checkPrefixCuts (2^48) 2030698497 9 Manual.Count131072.C015463.packed 128 cuts15463 = true := by
 decide +kernel
def pointBounds15463 : List (Nat × Nat × Nat) := [(2030761984,96667996100601,96668374398301),(2030825472,96668410108863,96668788406837)]
theorem point_links_checked15463 : (cuts15463.take 2).map (fun c => (2030698497-1+2*2^9*c.k,96667585960356+c.lower,96667964257789+c.upper)) = pointBounds15463 := by
 decide +kernel
def cuts15464 : List PrefixCut := [⟨58,386136599,386136852⟩,
⟨120,812038088,812038617⟩,
⟨128,867474999,867475564⟩]
theorem checked15464 : checkPrefixCuts (2^48) 2030829569 9 Manual.Count131072.C015464.packed 128 cuts15464 = true := by
 decide +kernel
def pointBounds15464 : List (Nat × Nat × Nat) := [(2030888960,96668822025265,96669200323509),(2030952448,96669247926754,96669626225274)]
theorem point_links_checked15464 : (cuts15464.take 2).map (fun c => (2030829569-1+2*2^9*c.k,96668435888666+c.lower,96668814186657+c.upper)) = pointBounds15464 := by
 decide +kernel
def cuts15465 : List PrefixCut := [⟨54,355483625,355483857⟩,
⟨116,764035306,764035805⟩,
⟨128,841226299,841226848⟩]
theorem checked15465 : checkPrefixCuts (2^48) 2030960641 9 Manual.Count131072.C015465.packed 128 cuts15465 = true := by
 decide +kernel
def pointBounds15465 : List (Nat × Nat × Nat) := [(2031015936,96669658847290,96670037146078),(2031079424,96670067398971,96670445698026)]
theorem point_links_checked15465 : (cuts15465.take 2).map (fun c => (2030960641-1+2*2^9*c.k,96669303363665+c.lower,96669681662221+c.upper)) = pointBounds15465 := by
 decide +kernel
def cuts15466 : List PrefixCut := [⟨50,324141685,324141896⟩,
⟨112,738349512,738349992⟩,
⟨128,843943412,843943961⟩]
theorem checked15466 : checkPrefixCuts (2^48) 2031091713 9 Manual.Count131072.C015466.packed 128 cuts15466 = true := by
 decide +kernel
def pointBounds15466 : List (Nat × Nat × Nat) := [(2031142912,96670468731649,96670847030965),(2031206400,96670882939476,96671261239061)]
theorem point_links_checked15466 : (cuts15466.take 2).map (fun c => (2031091713-1+2*2^9*c.k,96670144589964+c.lower,96670522889069+c.upper)) = pointBounds15466 := by
 decide +kernel
def cuts15467 : List PrefixCut := [⟨46,310263851,310264052⟩,
⟨108,704353261,704353723⟩,
⟨128,829616799,829617346⟩]
theorem checked15467 : checkPrefixCuts (2^48) 2031222785 9 Manual.Count131072.C015467.packed 128 cuts15467 = true := by
 decide +kernel
def pointBounds15467 : List (Nat × Nat × Nat) := [(2031269888,96671298797227,96671677097082),(2031333376,96671692886637,96672071186753)]
theorem point_links_checked15467 : (cuts15467.take 2).map (fun c => (2031222785-1+2*2^9*c.k,96670988533376+c.lower,96671366833030+c.upper)) = pointBounds15467 := by
 decide +kernel
def cuts15468 : List PrefixCut := [⟨42,275603180,275603363⟩,
⟨104,692530513,692530972⟩,
⟨128,851871157,851871720⟩]
theorem checked15468 : checkPrefixCuts (2^48) 2031353857 9 Manual.Count131072.C015468.packed 128 cuts15468 = true := by
 decide +kernel
def pointBounds15468 : List (Nat × Nat × Nat) := [(2031396864,96672093753355,96672472053739),(2031460352,96672510680688,96672888981348)]
theorem point_links_checked15468 : (cuts15468.take 2).map (fun c => (2031353857-1+2*2^9*c.k,96671818150175+c.lower,96672196450376+c.upper)) = pointBounds15468 := by
 decide +kernel
def cuts15469 : List PrefixCut := [⟨38,252447033,252447203⟩,
⟨100,667962713,667963161⟩,
⟨128,850153681,850154244⟩]
theorem checked15469 : checkPrefixCuts (2^48) 2031484929 9 Manual.Count131072.C015469.packed 128 cuts15469 = true := by
 decide +kernel
def pointBounds15469 : List (Nat × Nat × Nat) := [(2031523840,96672922468365,96673300769299),(2031587328,96673337984045,96673716285257)]
theorem point_links_checked15469 : (cuts15469.take 2).map (fun c => (2031484929-1+2*2^9*c.k,96672670021332+c.lower,96673048322096+c.upper)) = pointBounds15469 := by
 decide +kernel
def cuts15470 : List PrefixCut := [⟨34,221673757,221673907⟩,
⟨97,638133154,638133576⟩,
⟨128,846635007,846635566⟩]
theorem checked15470 : checkPrefixCuts (2^48) 2031616001 9 Manual.Count131072.C015470.packed 128 cuts15470 = true := by
 decide +kernel
def pointBounds15470 : List (Nat × Nat × Nat) := [(2031650816,96673741848770,96674120150247),(2031715328,96674158308167,96674536609916)]
theorem point_links_checked15470 : (cuts15470.take 2).map (fun c => (2031616001-1+2*2^9*c.k,96673520175013+c.lower,96673898476340+c.upper)) = pointBounds15470 := by
 decide +kernel
def cuts15471 : List PrefixCut := [⟨32,216672210,216672355⟩,
⟨95,630888653,630889069⟩,
⟨128,852399023,852399585⟩]
theorem checked15471 : checkPrefixCuts (2^48) 2031747073 9 Manual.Count131072.C015471.packed 128 cuts15471 = true := by
 decide +kernel
def pointBounds15471 : List (Nat × Nat × Nat) := [(2031779840,96674583482230,96674961784261),(2031844352,96674997698673,96675376000975)]
theorem point_links_checked15471 : (cuts15471.take 2).map (fun c => (2031747073-1+2*2^9*c.k,96674366810020+c.lower,96674745111906+c.upper)) = pointBounds15471 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000170
