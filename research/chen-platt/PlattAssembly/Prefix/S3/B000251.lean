import PlattAssemblyKernel
import PlattCertificates.Count131072.C028032
import PlattCertificates.Count131072.C028033
import PlattCertificates.Count131072.C028034
import PlattCertificates.Count131072.C028035
import PlattCertificates.Count131072.C028036
import PlattCertificates.Count131072.C028037
import PlattCertificates.Count131072.C028038
import PlattCertificates.Count131072.C028039
import PlattCertificates.Count131072.C028040
import PlattCertificates.Count131072.C028041
import PlattCertificates.Count131072.C028042
import PlattCertificates.Count131072.C028043
import PlattCertificates.Count131072.C028044
import PlattCertificates.Count131072.C028045
import PlattCertificates.Count131072.C028046
import PlattCertificates.Count131072.C028047
import PlattCertificates.Count131072.C028048
import PlattCertificates.Count131072.C028049
import PlattCertificates.Count131072.C028050
import PlattCertificates.Count131072.C028051
import PlattCertificates.Count131072.C028052
import PlattCertificates.Count131072.C028053
import PlattCertificates.Count131072.C028054
import PlattCertificates.Count131072.C028055
import PlattCertificates.Count131072.C028056
import PlattCertificates.Count131072.C028057
import PlattCertificates.Count131072.C028058
import PlattCertificates.Count131072.C028059
import PlattCertificates.Count131072.C028060
import PlattCertificates.Count131072.C028061
import PlattCertificates.Count131072.C028062
import PlattCertificates.Count131072.C028063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28032 : List PrefixCut := [⟨98,349108547,349108745⟩,
⟨128,457772581,457772839⟩]
theorem checked28032 : checkPrefixCuts (2^48) 3678142465 9 Manual.Count131072.C028032.packed 128 cuts28032 = true := by
 decide +kernel
def pointBounds28032 : List (Nat × Nat × Nat) := [(3678242816,104363513999490,104363896836334)]
theorem point_links_checked28032 : (cuts28032.take 1).map (fun c => (3678142465-1+2*2^9*c.k,104363164890943+c.lower,104363547727589+c.upper)) = pointBounds28032 := by
 decide +kernel
def cuts28033 : List PrefixCut := [⟨83,294306525,294306690⟩,
⟨128,451404949,451405205⟩]
theorem checked28033 : checkPrefixCuts (2^48) 3678273537 9 Manual.Count131072.C028033.packed 128 cuts28033 = true := by
 decide +kernel
def pointBounds28033 : List (Nat × Nat × Nat) := [(3678358528,104363916970049,104364299807118)]
theorem point_links_checked28033 : (cuts28033.take 1).map (fun c => (3678273537-1+2*2^9*c.k,104363622663524+c.lower,104364005500428+c.upper)) = pointBounds28033 := by
 decide +kernel
def cuts28034 : List PrefixCut := [⟨68,245553312,245553452⟩,
⟨128,464550210,464550467⟩]
theorem checked28034 : checkPrefixCuts (2^48) 3678404609 9 Manual.Count131072.C028034.packed 128 cuts28034 = true := by
 decide +kernel
def pointBounds28034 : List (Nat × Nat × Nat) := [(3678474240,104364319621785,104364702459085)]
theorem point_links_checked28034 : (cuts28034.take 1).map (fun c => (3678404609-1+2*2^9*c.k,104364074068473+c.lower,104364456905633+c.upper)) = pointBounds28034 := by
 decide +kernel
def cuts28035 : List PrefixCut := [⟨53,188233383,188233487⟩,
⟨128,448312174,448312426⟩]
theorem checked28035 : checkPrefixCuts (2^48) 3678535681 9 Manual.Count131072.C028035.packed 128 cuts28035 = true := by
 decide +kernel
def pointBounds28035 : List (Nat × Nat × Nat) := [(3678589952,104364726852066,104365109689587)]
theorem point_links_checked28035 : (cuts28035.take 1).map (fun c => (3678535681-1+2*2^9*c.k,104364538618683+c.lower,104364921456100+c.upper)) = pointBounds28035 := by
 decide +kernel
def cuts28036 : List PrefixCut := [⟨38,133901356,133901433⟩,
⟨128,452810467,452810726⟩]
theorem checked28036 : checkPrefixCuts (2^48) 3678666753 9 Manual.Count131072.C028036.packed 128 cuts28036 = true := by
 decide +kernel
def pointBounds28036 : List (Nat × Nat × Nat) := [(3678705664,104365120832213,104365503669959)]
theorem point_links_checked28036 : (cuts28036.take 1).map (fun c => (3678666753-1+2*2^9*c.k,104364986930857+c.lower,104365369768526+c.upper)) = pointBounds28036 := by
 decide +kernel
def cuts28037 : List PrefixCut := [⟨23,82633488,82633535⟩,
⟨128,449351337,449351593⟩]
theorem checked28037 : checkPrefixCuts (2^48) 3678797825 9 Manual.Count131072.C028037.packed 128 cuts28037 = true := by
 decide +kernel
def pointBounds28037 : List (Nat × Nat × Nat) := [(3678821376,104365522374812,104365905212787)]
theorem point_links_checked28037 : (cuts28037.take 1).map (fun c => (3678797825-1+2*2^9*c.k,104365439741324+c.lower,104365822579252+c.upper)) = pointBounds28037 := by
 decide +kernel
def cuts28038 : List PrefixCut := [⟨8,28920753,28920769⟩,
⟨121,432350814,432351059⟩,
⟨128,459357914,459358173⟩]
theorem checked28038 : checkPrefixCuts (2^48) 3678928897 9 Manual.Count131072.C028038.packed 128 cuts28038 = true := by
 decide +kernel
def pointBounds28038 : List (Nat × Nat × Nat) := [(3678937088,104365918013414,104366300851614),(3679052800,104366321443475,104366704281904)]
theorem point_links_checked28038 : (cuts28038.take 2).map (fun c => (3678928897-1+2*2^9*c.k,104365889092661+c.lower,104366271930845+c.upper)) = pointBounds28038 := by
 decide +kernel
def cuts28039 : List PrefixCut := [⟨106,378552488,378552697⟩,
⟨128,455210301,455210551⟩]
theorem checked28039 : checkPrefixCuts (2^48) 3679059969 9 Manual.Count131072.C028039.packed 128 cuts28039 = true := by
 decide +kernel
def pointBounds28039 : List (Nat × Nat × Nat) := [(3679168512,104366727003063,104367109841715)]
theorem point_links_checked28039 : (cuts28039.take 1).map (fun c => (3679059969-1+2*2^9*c.k,104366348450575+c.lower,104366731289018+c.upper)) = pointBounds28039 := by
 decide +kernel
def cuts28040 : List PrefixCut := [⟨91,319784996,319785178⟩,
⟨128,453663907,453664163⟩]
theorem checked28040 : checkPrefixCuts (2^48) 3679191041 9 Manual.Count131072.C028040.packed 128 cuts28040 = true := by
 decide +kernel
def pointBounds28040 : List (Nat × Nat × Nat) := [(3679284224,104367123445872,104367506284747)]
theorem point_links_checked28040 : (cuts28040.take 1).map (fun c => (3679191041-1+2*2^9*c.k,104366803660876+c.lower,104367186499569+c.upper)) = pointBounds28040 := by
 decide +kernel
def cuts28041 : List PrefixCut := [⟨76,270737122,270737274⟩,
⟨128,452882815,452883072⟩]
theorem checked28041 : checkPrefixCuts (2^48) 3679322113 9 Manual.Count131072.C028041.packed 128 cuts28041 = true := by
 decide +kernel
def pointBounds28041 : List (Nat × Nat × Nat) := [(3679399936,104367528061905,104367910901006)]
theorem point_links_checked28041 : (cuts28041.take 1).map (fun c => (3679322113-1+2*2^9*c.k,104367257324783+c.lower,104367640163732+c.upper)) = pointBounds28041 := by
 decide +kernel
def cuts28042 : List PrefixCut := [⟨61,215496159,215496282⟩,
⟨128,456309024,456309285⟩]
theorem checked28042 : checkPrefixCuts (2^48) 3679453185 9 Manual.Count131072.C028042.packed 128 cuts28042 = true := by
 decide +kernel
def pointBounds28042 : List (Nat × Nat × Nat) := [(3679515648,104367925703757,104368308543086)]
theorem point_links_checked28042 : (cuts28042.take 1).map (fun c => (3679453185-1+2*2^9*c.k,104367710207598+c.lower,104368093046804+c.upper)) = pointBounds28042 := by
 decide +kernel
def cuts28043 : List PrefixCut := [⟨46,165307633,165307723⟩,
⟨128,458052236,458052488⟩]
theorem checked28043 : checkPrefixCuts (2^48) 3679584257 9 Manual.Count131072.C028043.packed 128 cuts28043 = true := by
 decide +kernel
def pointBounds28043 : List (Nat × Nat × Nat) := [(3679631360,104368331824255,104368714663812)]
theorem point_links_checked28043 : (cuts28043.take 1).map (fun c => (3679584257-1+2*2^9*c.k,104368166516622+c.lower,104368549356089+c.upper)) = pointBounds28043 := by
 decide +kernel
def cuts28044 : List PrefixCut := [⟨31,109155987,109156049⟩,
⟨128,454670170,454670421⟩]
theorem checked28044 : checkPrefixCuts (2^48) 3679715329 9 Manual.Count131072.C028044.packed 128 cuts28044 = true := by
 decide +kernel
def pointBounds28044 : List (Nat × Nat × Nat) := [(3679747072,104368733724845,104369116564626)]
theorem point_links_checked28044 : (cuts28044.take 1).map (fun c => (3679715329-1+2*2^9*c.k,104368624568858+c.lower,104369007408577+c.upper)) = pointBounds28044 := by
 decide +kernel
def cuts28045 : List PrefixCut := [⟨16,56679657,56679689⟩,
⟨128,452053401,452053654⟩]
theorem checked28045 : checkPrefixCuts (2^48) 3679846401 9 Manual.Count131072.C028045.packed 128 cuts28045 = true := by
 decide +kernel
def pointBounds28045 : List (Nat × Nat × Nat) := [(3679862784,104369135918685,104369518758687)]
theorem point_links_checked28045 : (cuts28045.take 1).map (fun c => (3679846401-1+2*2^9*c.k,104369079239028+c.lower,104369462078998+c.upper)) = pointBounds28045 := by
 decide +kernel
def cuts28046 : List PrefixCut := [⟨1,4130363,4130365⟩,
⟨114,402474688,402474907⟩,
⟨128,451349011,451349258⟩]
theorem checked28046 : checkPrefixCuts (2^48) 3679977473 9 Manual.Count131072.C028046.packed 128 cuts28046 = true := by
 decide +kernel
def pointBounds28046 : List (Nat × Nat × Nat) := [(3679978496,104369535422792,104369918263017),(3680094208,104369933767117,104370316607559)]
theorem point_links_checked28046 : (cuts28046.take 2).map (fun c => (3679977473-1+2*2^9*c.k,104369531292429+c.lower,104369914132652+c.upper)) = pointBounds28046 := by
 decide +kernel
def cuts28047 : List PrefixCut := [⟨99,354734800,354735004⟩,
⟨128,458369360,458369623⟩]
theorem checked28047 : checkPrefixCuts (2^48) 3680108545 9 Manual.Count131072.C028047.packed 128 cuts28047 = true := by
 decide +kernel
def pointBounds28047 : List (Nat × Nat × Nat) := [(3680209920,104370337376240,104370720216914)]
theorem point_links_checked28047 : (cuts28047.take 1).map (fun c => (3680108545-1+2*2^9*c.k,104369982641440+c.lower,104370365481910+c.upper)) = pointBounds28047 := by
 decide +kernel
def cuts28048 : List PrefixCut := [⟨84,299120592,299120759⟩,
⟨128,459270781,459271040⟩]
theorem checked28048 : checkPrefixCuts (2^48) 3680239617 9 Manual.Count131072.C028048.packed 128 cuts28048 = true := by
 decide +kernel
def pointBounds28048 : List (Nat × Nat × Nat) := [(3680325632,104370740131392,104371122972292)]
theorem point_links_checked28048 : (cuts28048.take 1).map (fun c => (3680239617-1+2*2^9*c.k,104370441010800+c.lower,104370823851533+c.upper)) = pointBounds28048 := by
 decide +kernel
def cuts28049 : List PrefixCut := [⟨69,244121923,244122059⟩,
⟨128,452600786,452601040⟩]
theorem checked28049 : checkPrefixCuts (2^48) 3680370689 9 Manual.Count131072.C028049.packed 128 cuts28049 = true := by
 decide +kernel
def pointBounds28049 : List (Nat × Nat × Nat) := [(3680441344,104371144403504,104371527244632)]
theorem point_links_checked28049 : (cuts28049.take 1).map (fun c => (3680370689-1+2*2^9*c.k,104370900281581+c.lower,104371283122573+c.upper)) = pointBounds28049 := by
 decide +kernel
def cuts28050 : List PrefixCut := [⟨54,193639123,193639231⟩,
⟨128,459544016,459544273⟩]
theorem checked28050 : checkPrefixCuts (2^48) 3680501761 9 Manual.Count131072.C028050.packed 128 cuts28050 = true := by
 decide +kernel
def pointBounds28050 : List (Nat × Nat × Nat) := [(3680557056,104371546521490,104371929362844)]
theorem point_links_checked28050 : (cuts28050.take 1).map (fun c => (3680501761-1+2*2^9*c.k,104371352882367+c.lower,104371735723613+c.upper)) = pointBounds28050 := by
 decide +kernel
def cuts28051 : List PrefixCut := [⟨39,137271159,137271235⟩,
⟨128,452797967,452798221⟩]
theorem checked28051 : checkPrefixCuts (2^48) 3680632833 9 Manual.Count131072.C028051.packed 128 cuts28051 = true := by
 decide +kernel
def pointBounds28051 : List (Nat × Nat × Nat) := [(3680672768,104371949697542,104372332539121)]
theorem point_links_checked28051 : (cuts28051.take 1).map (fun c => (3680632833-1+2*2^9*c.k,104371812426383+c.lower,104372195267886+c.upper)) = pointBounds28051 := by
 decide +kernel
def cuts28052 : List PrefixCut := [⟨24,83430535,83430583⟩,
⟨128,452399530,452399786⟩]
theorem checked28052 : checkPrefixCuts (2^48) 3680763905 9 Manual.Count131072.C028052.packed 128 cuts28052 = true := by
 decide +kernel
def pointBounds28052 : List (Nat × Nat × Nat) := [(3680788480,104372348654885,104372731496690)]
theorem point_links_checked28052 : (cuts28052.take 1).map (fun c => (3680763905-1+2*2^9*c.k,104372265224350+c.lower,104372648066107+c.upper)) = pointBounds28052 := by
 decide +kernel
def cuts28053 : List PrefixCut := [⟨9,33952259,33952278⟩,
⟨122,429519907,429520146⟩,
⟨128,450930523,450930775⟩]
theorem checked28053 : checkPrefixCuts (2^48) 3680894977 9 Manual.Count131072.C028053.packed 128 cuts28053 = true := by
 decide +kernel
def pointBounds28053 : List (Nat × Nat × Nat) := [(3680904192,104372751576139,104373134418171),(3681019904,104373147143787,104373529986039)]
theorem point_links_checked28053 : (cuts28053.take 2).map (fun c => (3680894977-1+2*2^9*c.k,104372717623880+c.lower,104373100465893+c.upper)) = pointBounds28053 := by
 decide +kernel
def cuts28054 : List PrefixCut := [⟨107,383473377,383473591⟩,
⟨128,459478517,459478774⟩]
theorem checked28054 : checkPrefixCuts (2^48) 3681026049 9 Manual.Count131072.C028054.packed 128 cuts28054 = true := by
 decide +kernel
def pointBounds28054 : List (Nat × Nat × Nat) := [(3681135616,104373552027780,104373934870259)]
theorem point_links_checked28054 : (cuts28054.take 1).map (fun c => (3681026049-1+2*2^9*c.k,104373168554403+c.lower,104373551396668+c.upper)) = pointBounds28054 := by
 decide +kernel
def cuts28055 : List PrefixCut := [⟨92,328713250,328713432⟩,
⟨128,456633105,456633357⟩]
theorem checked28055 : checkPrefixCuts (2^48) 3681157121 9 Manual.Count131072.C028055.packed 128 cuts28055 = true := by
 decide +kernel
def pointBounds28055 : List (Nat × Nat × Nat) := [(3681251328,104373956746170,104374339588874)]
theorem point_links_checked28055 : (cuts28055.take 1).map (fun c => (3681157121-1+2*2^9*c.k,104373628032920+c.lower,104374010875442+c.upper)) = pointBounds28055 := by
 decide +kernel
def cuts28056 : List PrefixCut := [⟨77,275791780,275791931⟩,
⟨128,465180219,465180477⟩]
theorem checked28056 : checkPrefixCuts (2^48) 3681288193 9 Manual.Count131072.C028056.packed 128 cuts28056 = true := by
 decide +kernel
def pointBounds28056 : List (Nat × Nat × Nat) := [(3681367040,104374360457805,104374743300730)]
theorem point_links_checked28056 : (cuts28056.take 1).map (fun c => (3681288193-1+2*2^9*c.k,104374084666025+c.lower,104374467508799+c.upper)) = pointBounds28056 := by
 decide +kernel
def cuts28057 : List PrefixCut := [⟨62,221650574,221650698⟩,
⟨128,454536276,454536530⟩]
theorem checked28057 : checkPrefixCuts (2^48) 3681419265 9 Manual.Count131072.C028057.packed 128 cuts28057 = true := by
 decide +kernel
def pointBounds28057 : List (Nat × Nat × Nat) := [(3681482752,104374771496818,104375154339974)]
theorem point_links_checked28057 : (cuts28057.take 1).map (fun c => (3681419265-1+2*2^9*c.k,104374549846244+c.lower,104374932689276+c.upper)) = pointBounds28057 := by
 decide +kernel
def cuts28058 : List PrefixCut := [⟨47,164072506,164072600⟩,
⟨128,448556623,448556880⟩]
theorem checked28058 : checkPrefixCuts (2^48) 3681550337 9 Manual.Count131072.C028058.packed 128 cuts28058 = true := by
 decide +kernel
def pointBounds28058 : List (Nat × Nat × Nat) := [(3681598464,104375168455026,104375551298406)]
theorem point_links_checked28058 : (cuts28058.take 1).map (fun c => (3681550337-1+2*2^9*c.k,104375004382520+c.lower,104375387225806+c.upper)) = pointBounds28058 := by
 decide +kernel
def cuts28059 : List PrefixCut := [⟨32,112843844,112843906⟩,
⟨128,457103197,457103452⟩]
theorem checked28059 : checkPrefixCuts (2^48) 3681681409 9 Manual.Count131072.C028059.packed 128 cuts28059 = true := by
 decide +kernel
def pointBounds28059 : List (Nat × Nat × Nat) := [(3681714176,104375565782987,104375948626592)]
theorem point_links_checked28059 : (cuts28059.take 1).map (fun c => (3681681409-1+2*2^9*c.k,104375452939143+c.lower,104375835782686+c.upper)) = pointBounds28059 := by
 decide +kernel
def cuts28060 : List PrefixCut := [⟨17,58713530,58713565⟩,
⟨128,457469176,457469437⟩]
theorem checked28060 : checkPrefixCuts (2^48) 3681812481 9 Manual.Count131072.C028060.packed 128 cuts28060 = true := by
 decide +kernel
def pointBounds28060 : List (Nat × Nat × Nat) := [(3681829888,104375968755870,104376351599703)]
theorem point_links_checked28060 : (cuts28060.take 1).map (fun c => (3681812481-1+2*2^9*c.k,104375910042340+c.lower,104376292886138+c.upper)) = pointBounds28060 := by
 decide +kernel
def cuts28061 : List PrefixCut := [⟨2,6803814,6803818⟩,
⟨115,407152164,407152389⟩,
⟨128,455694601,455694855⟩]
theorem checked28061 : checkPrefixCuts (2^48) 3681943553 9 Manual.Count131072.C028061.packed 128 cuts28061 = true := by
 decide +kernel
def pointBounds28061 : List (Nat × Nat × Nat) := [(3681945600,104376374315330,104376757159393),(3682061312,104376774663680,104377157507964)]
theorem point_links_checked28061 : (cuts28061.take 2).map (fun c => (3681943553-1+2*2^9*c.k,104376367511516+c.lower,104376750355575+c.upper)) = pointBounds28061 := by
 decide +kernel
def cuts28062 : List PrefixCut := [⟨100,351564063,351564264⟩,
⟨128,452544244,452544504⟩]
theorem checked28062 : checkPrefixCuts (2^48) 3682074625 9 Manual.Count131072.C028062.packed 128 cuts28062 = true := by
 decide +kernel
def pointBounds28062 : List (Nat × Nat × Nat) := [(3682177024,104377174770180,104377557614694)]
theorem point_links_checked28062 : (cuts28062.take 1).map (fun c => (3682074625-1+2*2^9*c.k,104376823206117+c.lower,104377206050430+c.upper)) = pointBounds28062 := by
 decide +kernel
def cuts28063 : List PrefixCut := [⟨85,305152558,305152729⟩,
⟨128,458031875,458032130⟩]
theorem checked28063 : checkPrefixCuts (2^48) 3682205697 9 Manual.Count131072.C028063.packed 128 cuts28063 = true := by
 decide +kernel
def pointBounds28063 : List (Nat × Nat × Nat) := [(3682292736,104377580902919,104377963747663)]
theorem point_links_checked28063 : (cuts28063.take 1).map (fun c => (3682205697-1+2*2^9*c.k,104377275750361+c.lower,104377658594934+c.upper)) = pointBounds28063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000251
