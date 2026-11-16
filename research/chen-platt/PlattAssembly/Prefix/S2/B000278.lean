import PlattAssemblyKernel
import PlattCertificates.Count131072.C018896
import PlattCertificates.Count131072.C018897
import PlattCertificates.Count131072.C018898
import PlattCertificates.Count131072.C018899
import PlattCertificates.Count131072.C018900
import PlattCertificates.Count131072.C018901
import PlattCertificates.Count131072.C018902
import PlattCertificates.Count131072.C018903
import PlattCertificates.Count131072.C018904
import PlattCertificates.Count131072.C018905
import PlattCertificates.Count131072.C018906
import PlattCertificates.Count131072.C018907
import PlattCertificates.Count131072.C018908
import PlattCertificates.Count131072.C018909
import PlattCertificates.Count131072.C018910
import PlattCertificates.Count131072.C018911
import PlattCertificates.Count131072.C018912
import PlattCertificates.Count131072.C018913
import PlattCertificates.Count131072.C018914
import PlattCertificates.Count131072.C018915
import PlattCertificates.Count131072.C018916
import PlattCertificates.Count131072.C018917
import PlattCertificates.Count131072.C018918
import PlattCertificates.Count131072.C018919
import PlattCertificates.Count131072.C018920
import PlattCertificates.Count131072.C018921
import PlattCertificates.Count131072.C018922
import PlattCertificates.Count131072.C018923
import PlattCertificates.Count131072.C018924
import PlattCertificates.Count131072.C018925
import PlattCertificates.Count131072.C018926
import PlattCertificates.Count131072.C018927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18896 : List PrefixCut := [⟨10,57073960,57073991⟩,
⟨86,462371210,462371488⟩,
⟨128,692472834,692473246⟩]
theorem checked18896 : checkPrefixCuts (2^48) 2480668673 9 Manual.Count131072.C018896.packed 128 cuts18896 = true := by
 decide +kernel
def pointBounds18896 : List (Nat × Nat × Nat) := [(2480678912,99284083789271,99284463721759),(2480756736,99284489086521,99284869019256)]
theorem point_links_checked18896 : (cuts18896.take 2).map (fun c => (2480668673-1+2*2^9*c.k,99284026715311+c.lower,99284406647768+c.upper)) = pointBounds18896 := by
 decide +kernel
def cuts18897 : List PrefixCut := [⟨34,182671518,182671630⟩,
⟨110,594637451,594637811⟩,
⟨128,689032653,689033073⟩]
theorem checked18897 : checkPrefixCuts (2^48) 2480799745 9 Manual.Count131072.C018897.packed 128 cuts18897 = true := by
 decide +kernel
def pointBounds18897 : List (Nat × Nat × Nat) := [(2480834560,99284901859663,99285281792644),(2480912384,99285313825596,99285693758825)]
theorem point_links_checked18897 : (cuts18897.take 2).map (fun c => (2480799745-1+2*2^9*c.k,99284719188145+c.lower,99285099121014+c.upper)) = pointBounds18897 := by
 decide +kernel
def cuts18898 : List PrefixCut := [⟨58,300653049,300653232⟩,
⟨128,680600492,680600903⟩]
theorem checked18898 : checkPrefixCuts (2^48) 2480930817 9 Manual.Count131072.C018898.packed 128 cuts18898 = true := by
 decide +kernel
def pointBounds18898 : List (Nat × Nat × Nat) := [(2480990208,99285708873847,99286088807319)]
theorem point_links_checked18898 : (cuts18898.take 1).map (fun c => (2480930817-1+2*2^9*c.k,99285408220798+c.lower,99285788154087+c.upper)) = pointBounds18898 := by
 decide +kernel
def cuts18899 : List PrefixCut := [⟨6,32333031,32333050⟩,
⟨82,442104694,442104957⟩,
⟨128,692930363,692930780⟩]
theorem checked18899 : checkPrefixCuts (2^48) 2481061889 9 Manual.Count131072.C018899.packed 128 cuts18899 = true := by
 decide +kernel
def pointBounds18899 : List (Nat × Nat × Nat) := [(2481068032,99286121154321,99286501088040),(2481145856,99286530925984,99286910859947)]
theorem point_links_checked18899 : (cuts18899.take 2).map (fun c => (2481061889-1+2*2^9*c.k,99286088821290+c.lower,99286468754990+c.upper)) = pointBounds18899 := by
 decide +kernel
def cuts18900 : List PrefixCut := [⟨30,157118103,157118197⟩,
⟨106,568225337,568225682⟩,
⟨128,690284507,690284927⟩]
theorem checked18900 : checkPrefixCuts (2^48) 2481192961 9 Manual.Count131072.C018900.packed 128 cuts18900 = true := by
 decide +kernel
def pointBounds18900 : List (Nat × Nat × Nat) := [(2481223680,99286938869756,99287318803967),(2481301504,99287349976990,99287729911452)]
theorem point_links_checked18900 : (cuts18900.take 2).map (fun c => (2481192961-1+2*2^9*c.k,99286781751653+c.lower,99287161685770+c.upper)) = pointBounds18900 := by
 decide +kernel
def cuts18901 : List PrefixCut := [⟨54,285178419,285178595⟩,
⟨128,683555635,683556048⟩]
theorem checked18901 : checkPrefixCuts (2^48) 2481324033 9 Manual.Count131072.C018901.packed 128 cuts18901 = true := by
 decide +kernel
def pointBounds18901 : List (Nat × Nat × Nat) := [(2481379328,99287757214579,99288137149292)]
theorem point_links_checked18901 : (cuts18901.take 1).map (fun c => (2481324033-1+2*2^9*c.k,99287472036160+c.lower,99287851970697+c.upper)) = pointBounds18901 := by
 decide +kernel
def cuts18902 : List PrefixCut := [⟨2,11116271,11116278⟩,
⟨78,421390909,421391158⟩,
⟨128,691799834,691800249⟩]
theorem checked18902 : checkPrefixCuts (2^48) 2481455105 9 Manual.Count131072.C018902.packed 128 cuts18902 = true := by
 decide +kernel
def pointBounds18902 : List (Nat × Nat × Nat) := [(2481457152,99288166708066,99288546643023),(2481534976,99288576982704,99288956917903)]
theorem point_links_checked18902 : (cuts18902.take 2).map (fun c => (2481455105-1+2*2^9*c.k,99288155591795+c.lower,99288535526745+c.upper)) = pointBounds18902 := by
 decide +kernel
def cuts18903 : List PrefixCut := [⟨26,142348106,142348190⟩,
⟨102,555545865,555546194⟩,
⟨128,694939059,694939476⟩]
theorem checked18903 : checkPrefixCuts (2^48) 2481586177 9 Manual.Count131072.C018903.packed 128 cuts18903 = true := by
 decide +kernel
def pointBounds18903 : List (Nat × Nat × Nat) := [(2481612800,99288989739735,99289369675184),(2481690624,99289402937494,99289782873188)]
theorem point_links_checked18903 : (cuts18903.take 2).map (fun c => (2481586177-1+2*2^9*c.k,99288847391629+c.lower,99289227326994+c.upper)) = pointBounds18903 := by
 decide +kernel
def cuts18904 : List PrefixCut := [⟨50,267326715,267326876⟩,
⟨126,672105845,672106255⟩,
⟨128,683447191,683447608⟩]
theorem checked18904 : checkPrefixCuts (2^48) 2481717249 9 Manual.Count131072.C018904.packed 128 cuts18904 = true := by
 decide +kernel
def pointBounds18904 : List (Nat × Nat × Nat) := [(2481768448,99289809657403,99290189593346),(2481846272,99290214436533,99290594372725)]
theorem point_links_checked18904 : (cuts18904.take 2).map (fun c => (2481717249-1+2*2^9*c.k,99289542330688+c.lower,99289922266470+c.upper)) = pointBounds18904 := by
 decide +kernel
def cuts18905 : List PrefixCut := [⟨74,400229792,400230039⟩,
⟨128,684999004,684999421⟩]
theorem checked18905 : checkPrefixCuts (2^48) 2481848321 9 Manual.Count131072.C018905.packed 128 cuts18905 = true := by
 decide +kernel
def pointBounds18905 : List (Nat × Nat × Nat) := [(2481924096,99290626007671,99291005944117)]
theorem point_links_checked18905 : (cuts18905.take 1).map (fun c => (2481848321-1+2*2^9*c.k,99290225777879+c.lower,99290605714078+c.upper)) = pointBounds18905 := by
 decide +kernel
def cuts18906 : List PrefixCut := [⟨22,122366048,122366119⟩,
⟨98,536066066,536066388⟩,
⟨128,694262040,694262456⟩]
theorem checked18906 : checkPrefixCuts (2^48) 2481979393 9 Manual.Count131072.C018906.packed 128 cuts18906 = true := by
 decide +kernel
def pointBounds18906 : List (Nat × Nat × Nat) := [(2482001920,99291033142931,99291413079618),(2482079744,99291446842949,99291826779887)]
theorem point_links_checked18906 : (cuts18906.take 2).map (fun c => (2481979393-1+2*2^9*c.k,99290910776883+c.lower,99291290713499+c.upper)) = pointBounds18906 := by
 decide +kernel
def cuts18907 : List PrefixCut := [⟨46,248233377,248233525⟩,
⟨122,661340541,661340935⟩,
⟨128,692864515,692864928⟩]
theorem checked18907 : checkPrefixCuts (2^48) 2482110465 9 Manual.Count131072.C018907.packed 128 cuts18907 = true := by
 decide +kernel
def pointBounds18907 : List (Nat × Nat × Nat) := [(2482157568,99291853272300,99292233209480),(2482235392,99292266379464,99292646316890)]
theorem point_links_checked18907 : (cuts18907.take 2).map (fun c => (2482110465-1+2*2^9*c.k,99291605038923+c.lower,99291984975955+c.upper)) = pointBounds18907 := by
 decide +kernel
def cuts18908 : List PrefixCut := [⟨70,379075504,379075731⟩,
⟨128,692374257,692374669⟩]
theorem checked18908 : checkPrefixCuts (2^48) 2482241537 9 Manual.Count131072.C018908.packed 128 cuts18908 = true := by
 decide +kernel
def pointBounds18908 : List (Nat × Nat × Nat) := [(2482313216,99292676978942,99293056916614)]
theorem point_links_checked18908 : (cuts18908.take 1).map (fun c => (2482241537-1+2*2^9*c.k,99292297903438+c.lower,99292677840883+c.upper)) = pointBounds18908 := by
 decide +kernel
def cuts18909 : List PrefixCut := [⟨18,93999516,93999573⟩,
⟨94,501738582,501738885⟩,
⟨128,683493593,683494003⟩]
theorem checked18909 : checkPrefixCuts (2^48) 2482372609 9 Manual.Count131072.C018909.packed 128 cuts18909 = true := by
 decide +kernel
def pointBounds18909 : List (Nat × Nat × Nat) := [(2482391040,99293084277211,99293464215125),(2482468864,99293492016277,99293871954437)]
theorem point_links_checked18909 : (cuts18909.take 2).map (fun c => (2482372609-1+2*2^9*c.k,99292990277695+c.lower,99293370215552+c.upper)) = pointBounds18909 := by
 decide +kernel
def cuts18910 : List PrefixCut := [⟨42,223476899,223477030⟩,
⟨118,627108765,627109142⟩,
⟨128,679375896,679376304⟩]
theorem checked18910 : checkPrefixCuts (2^48) 2482503681 9 Manual.Count131072.C018910.packed 128 cuts18910 = true := by
 decide +kernel
def pointBounds18910 : List (Nat × Nat × Nat) := [(2482546688,99293897248187,99294277186585),(2482624512,99294300880053,99294680818697)]
theorem point_links_checked18910 : (cuts18910.take 2).map (fun c => (2482503681-1+2*2^9*c.k,99293673771288+c.lower,99294053709555+c.upper)) = pointBounds18910 := by
 decide +kernel
def cuts18911 : List PrefixCut := [⟨66,347043772,347043979⟩,
⟨128,672877595,672877999⟩]
theorem checked18911 : checkPrefixCuts (2^48) 2482634753 9 Manual.Count131072.C018911.packed 128 cuts18911 = true := by
 decide +kernel
def pointBounds18911 : List (Nat × Nat × Nat) := [(2482702336,99294700190956,99295080129838)]
theorem point_links_checked18911 : (cuts18911.take 1).map (fun c => (2482634753-1+2*2^9*c.k,99294353147184+c.lower,99294733085859+c.upper)) = pointBounds18911 := by
 decide +kernel
def cuts18912 : List PrefixCut := [⟨14,76638921,76638966⟩,
⟨90,483747214,483747507⟩,
⟨128,690527541,690527959⟩]
theorem checked18912 : checkPrefixCuts (2^48) 2482765825 9 Manual.Count131072.C018912.packed 128 cuts18912 = true := by
 decide +kernel
def pointBounds18912 : List (Nat × Nat × Nat) := [(2482780160,99295102663700,99295482602824),(2482857984,99295509771993,99295889711365)]
theorem point_links_checked18912 : (cuts18912.take 2).map (fun c => (2482765825-1+2*2^9*c.k,99295026024779+c.lower,99295405963858+c.upper)) = pointBounds18912 := by
 decide +kernel
def cuts18913 : List PrefixCut := [⟨38,202922685,202922811⟩,
⟨114,611139105,611139473⟩,
⟨128,685956619,685957032⟩]
theorem checked18913 : checkPrefixCuts (2^48) 2482896897 9 Manual.Count131072.C018913.packed 128 cuts18913 = true := by
 decide +kernel
def pointBounds18913 : List (Nat × Nat × Nat) := [(2482935808,99295919475005,99296299414628),(2483013632,99296327691425,99296707631290)]
theorem point_links_checked18913 : (cuts18913.take 2).map (fun c => (2482896897-1+2*2^9*c.k,99295716552320+c.lower,99296096491817+c.upper)) = pointBounds18913 := by
 decide +kernel
def cuts18914 : List PrefixCut := [⟨62,330098756,330098952⟩,
⟨128,690001207,690001619⟩]
theorem checked18914 : checkPrefixCuts (2^48) 2483027969 9 Manual.Count131072.C018914.packed 128 cuts18914 = true := by
 decide +kernel
def pointBounds18914 : List (Nat × Nat × Nat) := [(2483091456,99296732607695,99297112547801)]
theorem point_links_checked18914 : (cuts18914.take 1).map (fun c => (2483027969-1+2*2^9*c.k,99296402508939+c.lower,99296782448849+c.upper)) = pointBounds18914 := by
 decide +kernel
def cuts18915 : List PrefixCut := [⟨10,53389413,53389444⟩,
⟨86,451705950,451706215⟩,
⟨128,677949636,677950034⟩]
theorem checked18915 : checkPrefixCuts (2^48) 2483159041 9 Manual.Count131072.C018915.packed 128 cuts18915 = true := by
 decide +kernel
def pointBounds18915 : List (Nat × Nat × Nat) := [(2483169280,99297145899559,99297525839912),(2483247104,99297544216096,99297924156683)]
theorem point_links_checked18915 : (cuts18915.take 2).map (fun c => (2483159041-1+2*2^9*c.k,99297092510146+c.lower,99297472450468+c.upper)) = pointBounds18915 := by
 decide +kernel
def cuts18916 : List PrefixCut := [⟨34,179314607,179314714⟩,
⟨110,587353741,587354095⟩,
⟨128,683354418,683354831⟩]
theorem checked18916 : checkPrefixCuts (2^48) 2483290113 9 Manual.Count131072.C018916.packed 128 cuts18916 = true := by
 decide +kernel
def pointBounds18916 : List (Nat × Nat × Nat) := [(2483324928,99297949774389,99298329715216),(2483402752,99298357813523,99298737754597)]
theorem point_links_checked18916 : (cuts18916.take 2).map (fun c => (2483290113-1+2*2^9*c.k,99297770459782+c.lower,99298150400502+c.upper)) = pointBounds18916 := by
 decide +kernel
def cuts18917 : List PrefixCut := [⟨58,309418866,309419049⟩,
⟨128,688078588,688078997⟩]
theorem checked18917 : checkPrefixCuts (2^48) 2483421185 9 Manual.Count131072.C018917.packed 128 cuts18917 = true := by
 decide +kernel
def pointBounds18917 : List (Nat × Nat × Nat) := [(2483480576,99298763233066,99299143174382)]
theorem point_links_checked18917 : (cuts18917.take 1).map (fun c => (2483421185-1+2*2^9*c.k,99298453814200+c.lower,99298833755333+c.upper)) = pointBounds18917 := by
 decide +kernel
def cuts18918 : List PrefixCut := [⟨6,34680651,34680672⟩,
⟨82,442454726,442454989⟩,
⟨128,691668958,691669370⟩]
theorem checked18918 : checkPrefixCuts (2^48) 2483552257 9 Manual.Count131072.C018918.packed 128 cuts18918 = true := by
 decide +kernel
def pointBounds18918 : List (Nat × Nat × Nat) := [(2483558400,99299176573439,99299556515002),(2483636224,99299584347514,99299964289319)]
theorem point_links_checked18918 : (cuts18918.take 2).map (fun c => (2483552257-1+2*2^9*c.k,99299141892788+c.lower,99299521834330+c.upper)) = pointBounds18918 := by
 decide +kernel
def cuts18919 : List PrefixCut := [⟨30,159340461,159340556⟩,
⟨106,573435251,573435596⟩,
⟨128,690952389,690952803⟩]
theorem checked18919 : checkPrefixCuts (2^48) 2483683329 9 Manual.Count131072.C018919.packed 128 cuts18919 = true := by
 decide +kernel
def pointBounds18919 : List (Nat × Nat × Nat) := [(2483714048,99299992902207,99300372844256),(2483791872,99300406996997,99300786939296)]
theorem point_links_checked18919 : (cuts18919.take 2).map (fun c => (2483683329-1+2*2^9*c.k,99299833561746+c.lower,99300213503700+c.upper)) = pointBounds18919 := by
 decide +kernel
def cuts18920 : List PrefixCut := [⟨54,292825040,292825215⟩,
⟨128,696468747,696469158⟩]
theorem checked18920 : checkPrefixCuts (2^48) 2483814401 9 Manual.Count131072.C018920.packed 128 cuts18920 = true := by
 decide +kernel
def pointBounds18920 : List (Nat × Nat × Nat) := [(2483869696,99300817339175,99301197281718)]
theorem point_links_checked18920 : (cuts18920.take 1).map (fun c => (2483814401-1+2*2^9*c.k,99300524514135+c.lower,99300904456503+c.upper)) = pointBounds18920 := by
 decide +kernel
def cuts18921 : List PrefixCut := [⟨2,12124985,12124992⟩,
⟨78,420741706,420741956⟩,
⟨128,686347034,686347445⟩]
theorem checked18921 : checkPrefixCuts (2^48) 2483945473 9 Manual.Count131072.C018921.packed 128 cuts18921 = true := by
 decide +kernel
def pointBounds18921 : List (Nat × Nat × Nat) := [(2483947520,99301233107867,99301613050653),(2484025344,99301641724588,99302021667617)]
theorem point_links_checked18921 : (cuts18921.take 2).map (fun c => (2483945473-1+2*2^9*c.k,99301220982882+c.lower,99301600925661+c.upper)) = pointBounds18921 := by
 decide +kernel
def cuts18922 : List PrefixCut := [⟨26,135633362,135633442⟩,
⟨102,533006914,533007237⟩,
⟨128,670900677,670901085⟩]
theorem checked18922 : checkPrefixCuts (2^48) 2484076545 9 Manual.Count131072.C018922.packed 128 cuts18922 = true := by
 decide +kernel
def pointBounds18922 : List (Nat × Nat × Nat) := [(2484103168,99302042963278,99302422906548),(2484180992,99302440336830,99302820280343)]
theorem point_links_checked18922 : (cuts18922.take 2).map (fun c => (2484076545-1+2*2^9*c.k,99301907329916+c.lower,99302287273106+c.upper)) = pointBounds18922 := by
 decide +kernel
def cuts18923 : List PrefixCut := [⟨50,271137795,271137955⟩,
⟨126,677324040,677324452⟩,
⟨128,686388021,686388439⟩]
theorem checked18923 : checkPrefixCuts (2^48) 2484207617 9 Manual.Count131072.C018923.packed 128 cuts18923 = true := by
 decide +kernel
def pointBounds18923 : List (Nat × Nat × Nat) := [(2484258816,99302849368388,99303229312146),(2484336640,99303255554633,99303635498643)]
theorem point_links_checked18923 : (cuts18923.take 2).map (fun c => (2484207617-1+2*2^9*c.k,99302578230593+c.lower,99302958174191+c.upper)) = pointBounds18923 := by
 decide +kernel
def cuts18924 : List PrefixCut := [⟨74,397675991,397676224⟩,
⟨128,686691557,686691962⟩]
theorem checked18924 : checkPrefixCuts (2^48) 2484338689 9 Manual.Count131072.C018924.packed 128 cuts18924 = true := by
 decide +kernel
def pointBounds18924 : List (Nat × Nat × Nat) := [(2484414464,99303662294605,99304042238854)]
theorem point_links_checked18924 : (cuts18924.take 1).map (fun c => (2484338689-1+2*2^9*c.k,99303264618614+c.lower,99303644562630+c.upper)) = pointBounds18924 := by
 decide +kernel
def cuts18925 : List PrefixCut := [⟨22,120997184,120997255⟩,
⟨98,527825009,527825326⟩,
⟨128,689600953,689601369⟩]
theorem checked18925 : checkPrefixCuts (2^48) 2484469761 9 Manual.Count131072.C018925.packed 128 cuts18925 = true := by
 decide +kernel
def pointBounds18925 : List (Nat × Nat × Nat) := [(2484492288,99304072307355,99304452251847),(2484570112,99304479135180,99304859079918)]
theorem point_links_checked18925 : (cuts18925.take 2).map (fun c => (2484469761-1+2*2^9*c.k,99303951310171+c.lower,99304331254592+c.upper)) = pointBounds18925 := by
 decide +kernel
def cuts18926 : List PrefixCut := [⟨46,244585969,244586120⟩,
⟨122,656712627,656713024⟩,
⟨128,687978439,687978856⟩]
theorem checked18926 : checkPrefixCuts (2^48) 2484600833 9 Manual.Count131072.C018926.packed 128 cuts18926 = true := by
 decide +kernel
def pointBounds18926 : List (Nat × Nat × Nat) := [(2484647936,99304885497093,99305265442081),(2484725760,99305297623751,99305677568985)]
theorem point_links_checked18926 : (cuts18926.take 2).map (fun c => (2484600833-1+2*2^9*c.k,99304640911124+c.lower,99305020855961+c.upper)) = pointBounds18926 := by
 decide +kernel
def cuts18927 : List PrefixCut := [⟨70,380734603,380734833⟩,
⟨128,695191981,695192395⟩]
theorem checked18927 : checkPrefixCuts (2^48) 2484731905 9 Manual.Count131072.C018927.packed 128 cuts18927 = true := by
 decide +kernel
def pointBounds18927 : List (Nat × Nat × Nat) := [(2484803584,99305709624166,99306089569650)]
theorem point_links_checked18927 : (cuts18927.take 1).map (fun c => (2484731905-1+2*2^9*c.k,99305328889563+c.lower,99305708834817+c.upper)) = pointBounds18927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000278
