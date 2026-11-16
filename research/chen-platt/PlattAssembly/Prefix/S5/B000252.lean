import PlattAssemblyKernel
import PlattCertificates.Count131072.C048064
import PlattCertificates.Count131072.C048065
import PlattCertificates.Count131072.C048066
import PlattCertificates.Count131072.C048067
import PlattCertificates.Count131072.C048068
import PlattCertificates.Count131072.C048069
import PlattCertificates.Count131072.C048070
import PlattCertificates.Count131072.C048071
import PlattCertificates.Count131072.C048072
import PlattCertificates.Count131072.C048073
import PlattCertificates.Count131072.C048074
import PlattCertificates.Count131072.C048075
import PlattCertificates.Count131072.C048076
import PlattCertificates.Count131072.C048077
import PlattCertificates.Count131072.C048078
import PlattCertificates.Count131072.C048079
import PlattCertificates.Count131072.C048080
import PlattCertificates.Count131072.C048081
import PlattCertificates.Count131072.C048082
import PlattCertificates.Count131072.C048083
import PlattCertificates.Count131072.C048084
import PlattCertificates.Count131072.C048085
import PlattCertificates.Count131072.C048086
import PlattCertificates.Count131072.C048087
import PlattCertificates.Count131072.C048088
import PlattCertificates.Count131072.C048089
import PlattCertificates.Count131072.C048090
import PlattCertificates.Count131072.C048091
import PlattCertificates.Count131072.C048092
import PlattCertificates.Count131072.C048093
import PlattCertificates.Count131072.C048094
import PlattCertificates.Count131072.C048095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48064 : List PrefixCut := [⟨64,264425151,264425299⟩]
theorem checked48064 : checkPrefixCuts (2^48) 6303776769 10 Manual.Count131072.C048064.packed 64 cuts48064 = true := by
 decide +kernel
def cuts48065 : List PrefixCut := [⟨14,55366941,55366973⟩,
⟨64,257632761,257632912⟩]
theorem checked48065 : checkPrefixCuts (2^48) 6303907841 10 Manual.Count131072.C048065.packed 64 cuts48065 = true := by
 decide +kernel
def pointBounds48065 : List (Nat × Nat × Nat) := [(6303936512,111165359298509,111165746140056)]
theorem point_links_checked48065 : (cuts48065.take 1).map (fun c => (6303907841-1+2*2^10*c.k,111165303931568+c.lower,111165690773083+c.upper)) = pointBounds48065 := by
 decide +kernel
def cuts48066 : List PrefixCut := [⟨47,189894711,189894817⟩,
⟨64,258922258,258922406⟩]
theorem checked48066 : checkPrefixCuts (2^48) 6304038913 10 Manual.Count131072.C048066.packed 64 cuts48066 = true := by
 decide +kernel
def pointBounds48066 : List (Nat × Nat × Nat) := [(6304135168,111165751459040,111166138300812)]
theorem point_links_checked48066 : (cuts48066.take 1).map (fun c => (6304038913-1+2*2^10*c.k,111165561564329+c.lower,111165948405995+c.upper)) = pointBounds48066 := by
 decide +kernel
def cuts48067 : List PrefixCut := [⟨64,258336431,258336578⟩]
theorem checked48067 : checkPrefixCuts (2^48) 6304169985 10 Manual.Count131072.C048067.packed 64 cuts48067 = true := by
 decide +kernel
def cuts48068 : List PrefixCut := [⟨16,65721794,65721832⟩,
⟨64,256321942,256322092⟩]
theorem checked48068 : checkPrefixCuts (2^48) 6304301057 10 Manual.Count131072.C048068.packed 64 cuts48068 = true := by
 decide +kernel
def pointBounds48068 : List (Nat × Nat × Nat) := [(6304333824,111166144544812,111166531386811)]
theorem point_links_checked48068 : (cuts48068.take 1).map (fun c => (6304301057-1+2*2^10*c.k,111166078823018+c.lower,111166465664979+c.upper)) = pointBounds48068 := by
 decide +kernel
def cuts48069 : List PrefixCut := [⟨49,197695988,197696102⟩,
⟨64,255512982,255513127⟩]
theorem checked48069 : checkPrefixCuts (2^48) 6304432129 10 Manual.Count131072.C048069.packed 64 cuts48069 = true := by
 decide +kernel
def pointBounds48069 : List (Nat × Nat × Nat) := [(6304532480,111166532840948,111166919683173)]
theorem point_links_checked48069 : (cuts48069.take 1).map (fun c => (6304432129-1+2*2^10*c.k,111166335144960+c.lower,111166721987071+c.upper)) = pointBounds48069 := by
 decide +kernel
def cuts48070 : List PrefixCut := [⟨64,261445511,261445663⟩]
theorem checked48070 : checkPrefixCuts (2^48) 6304563201 10 Manual.Count131072.C048070.packed 64 cuts48070 = true := by
 decide +kernel
def cuts48071 : List PrefixCut := [⟨18,72414445,72414486⟩,
⟨64,259207827,259207981⟩]
theorem checked48071 : checkPrefixCuts (2^48) 6304694273 10 Manual.Count131072.C048071.packed 64 cuts48071 = true := by
 decide +kernel
def pointBounds48071 : List (Nat × Nat × Nat) := [(6304731136,111166924517898,111167311360347)]
theorem point_links_checked48071 : (cuts48071.take 1).map (fun c => (6304694273-1+2*2^10*c.k,111166852103453+c.lower,111167238945861+c.upper)) = pointBounds48071 := by
 decide +kernel
def cuts48072 : List PrefixCut := [⟨51,203978386,203978502⟩,
⟨64,256568461,256568608⟩]
theorem checked48072 : checkPrefixCuts (2^48) 6304825345 10 Manual.Count131072.C048072.packed 64 cuts48072 = true := by
 decide +kernel
def pointBounds48072 : List (Nat × Nat × Nat) := [(6304929792,111167315289666,111167702132344)]
theorem point_links_checked48072 : (cuts48072.take 1).map (fun c => (6304825345-1+2*2^10*c.k,111167111311280+c.lower,111167498153842+c.upper)) = pointBounds48072 := by
 decide +kernel
def cuts48073 : List PrefixCut := [⟨64,256920283,256920431⟩]
theorem checked48073 : checkPrefixCuts (2^48) 6304956417 10 Manual.Count131072.C048073.packed 64 cuts48073 = true := by
 decide +kernel
def cuts48074 : List PrefixCut := [⟨20,80936598,80936645⟩,
⟨64,260709500,260709650⟩]
theorem checked48074 : checkPrefixCuts (2^48) 6305087489 10 Manual.Count131072.C048074.packed 64 cuts48074 = true := by
 decide +kernel
def pointBounds48074 : List (Nat × Nat × Nat) := [(6305128448,111167705736622,111168092579526)]
theorem point_links_checked48074 : (cuts48074.take 1).map (fun c => (6305087489-1+2*2^10*c.k,111167624800024+c.lower,111168011642881+c.upper)) = pointBounds48074 := by
 decide +kernel
def cuts48075 : List PrefixCut := [⟨53,214411646,214411773⟩,
⟨64,258472044,258472199⟩]
theorem checked48075 : checkPrefixCuts (2^48) 6305218561 10 Manual.Count131072.C048075.packed 64 cuts48075 = true := by
 decide +kernel
def pointBounds48075 : List (Nat × Nat × Nat) := [(6305327104,111168099921170,111168486764304)]
theorem point_links_checked48075 : (cuts48075.take 1).map (fun c => (6305218561-1+2*2^10*c.k,111167885509524+c.lower,111168272352531+c.upper)) = pointBounds48075 := by
 decide +kernel
def cuts48076 : List PrefixCut := [⟨64,258779137,258779287⟩]
theorem checked48076 : checkPrefixCuts (2^48) 6305349633 10 Manual.Count131072.C048076.packed 64 cuts48076 = true := by
 decide +kernel
def cuts48077 : List PrefixCut := [⟨22,90305835,90305885⟩,
⟨64,260246876,260247023⟩]
theorem checked48077 : checkPrefixCuts (2^48) 6305480705 10 Manual.Count131072.C048077.packed 64 cuts48077 = true := by
 decide +kernel
def pointBounds48077 : List (Nat × Nat × Nat) := [(6305525760,111168493066540,111168879909902)]
theorem point_links_checked48077 : (cuts48077.take 1).map (fun c => (6305480705-1+2*2^10*c.k,111168402760705+c.lower,111168789604017+c.upper)) = pointBounds48077 := by
 decide +kernel
def cuts48078 : List PrefixCut := [⟨55,223682990,223683115⟩,
⟨64,260732471,260732617⟩]
theorem checked48078 : checkPrefixCuts (2^48) 6305611777 10 Manual.Count131072.C048078.packed 64 cuts48078 = true := by
 decide +kernel
def pointBounds48078 : List (Nat × Nat × Nat) := [(6305724416,111168886690571,111169273534155)]
theorem point_links_checked48078 : (cuts48078.take 1).map (fun c => (6305611777-1+2*2^10*c.k,111168663007581+c.lower,111169049851040+c.upper)) = pointBounds48078 := by
 decide +kernel
def cuts48079 : List PrefixCut := [⟨64,260057489,260057642⟩]
theorem checked48079 : checkPrefixCuts (2^48) 6305742849 10 Manual.Count131072.C048079.packed 64 cuts48079 = true := by
 decide +kernel
def cuts48080 : List PrefixCut := [⟨24,96549314,96549369⟩,
⟨64,262373174,262373321⟩]
theorem checked48080 : checkPrefixCuts (2^48) 6305873921 10 Manual.Count131072.C048080.packed 64 cuts48080 = true := by
 decide +kernel
def pointBounds48080 : List (Nat × Nat × Nat) := [(6305923072,111169280346855,111169667190668)]
theorem point_links_checked48080 : (cuts48080.take 1).map (fun c => (6305873921-1+2*2^10*c.k,111169183797541+c.lower,111169570641299+c.upper)) = pointBounds48080 := by
 decide +kernel
def cuts48081 : List PrefixCut := [⟨57,230632105,230632241⟩,
⟨64,259109320,259109471⟩]
theorem checked48081 : checkPrefixCuts (2^48) 6306004993 10 Manual.Count131072.C048081.packed 64 cuts48081 = true := by
 decide +kernel
def pointBounds48081 : List (Nat × Nat × Nat) := [(6306121728,111169676802820,111170063646861)]
theorem point_links_checked48081 : (cuts48081.take 1).map (fun c => (6306004993-1+2*2^10*c.k,111169446170715+c.lower,111169833014620+c.upper)) = pointBounds48081 := by
 decide +kernel
def cuts48082 : List PrefixCut := [⟨64,260933965,260934114⟩]
theorem checked48082 : checkPrefixCuts (2^48) 6306136065 10 Manual.Count131072.C048082.packed 64 cuts48082 = true := by
 decide +kernel
def cuts48083 : List PrefixCut := [⟨26,105603963,105604023⟩,
⟨64,259232476,259232627⟩]
theorem checked48083 : checkPrefixCuts (2^48) 6306267137 10 Manual.Count131072.C048083.packed 64 cuts48083 = true := by
 decide +kernel
def pointBounds48083 : List (Nat × Nat × Nat) := [(6306320384,111170071817963,111170458662228)]
theorem point_links_checked48083 : (cuts48083.take 1).map (fun c => (6306267137-1+2*2^10*c.k,111169966214000+c.lower,111170353058205+c.upper)) = pointBounds48083 := by
 decide +kernel
def cuts48084 : List PrefixCut := [⟨59,236776993,236777127⟩,
⟨64,256370588,256370733⟩]
theorem checked48084 : checkPrefixCuts (2^48) 6306398209 10 Manual.Count131072.C048084.packed 64 cuts48084 = true := by
 decide +kernel
def pointBounds48084 : List (Nat × Nat × Nat) := [(6306519040,111170462223469,111170849067959)]
theorem point_links_checked48084 : (cuts48084.take 1).map (fun c => (6306398209-1+2*2^10*c.k,111170225446476+c.lower,111170612290832+c.upper)) = pointBounds48084 := by
 decide +kernel
def cuts48085 : List PrefixCut := [⟨64,258239812,258239964⟩]
theorem checked48085 : checkPrefixCuts (2^48) 6306529281 10 Manual.Count131072.C048085.packed 64 cuts48085 = true := by
 decide +kernel
def cuts48086 : List PrefixCut := [⟨28,115996409,115996473⟩,
⟨64,260465987,260466136⟩]
theorem checked48086 : checkPrefixCuts (2^48) 6306660353 10 Manual.Count131072.C048086.packed 64 cuts48086 = true := by
 decide +kernel
def pointBounds48086 : List (Nat × Nat × Nat) := [(6306717696,111170856053285,111171242898002)]
theorem point_links_checked48086 : (cuts48086.take 1).map (fun c => (6306660353-1+2*2^10*c.k,111170740056876+c.lower,111171126901529+c.upper)) = pointBounds48086 := by
 decide +kernel
def cuts48087 : List PrefixCut := [⟨61,247294809,247294960⟩,
⟨64,259032378,259032535⟩]
theorem checked48087 : checkPrefixCuts (2^48) 6306791425 10 Manual.Count131072.C048087.packed 64 cuts48087 = true := by
 decide +kernel
def pointBounds48087 : List (Nat × Nat × Nat) := [(6306916352,111171247817672,111171634662625)]
theorem point_links_checked48087 : (cuts48087.take 1).map (fun c => (6306791425-1+2*2^10*c.k,111171000522863+c.lower,111171387367665+c.upper)) = pointBounds48087 := by
 decide +kernel
def cuts48088 : List PrefixCut := [⟨64,261927893,261928040⟩]
theorem checked48088 : checkPrefixCuts (2^48) 6306922497 10 Manual.Count131072.C048088.packed 64 cuts48088 = true := by
 decide +kernel
def cuts48089 : List PrefixCut := [⟨30,120942877,120942949⟩,
⟨64,259289390,259289546⟩]
theorem checked48089 : checkPrefixCuts (2^48) 6307053569 10 Manual.Count131072.C048089.packed 64 cuts48089 = true := by
 decide +kernel
def pointBounds48089 : List (Nat × Nat × Nat) := [(6307115008,111171642426011,111172029271189)]
theorem point_links_checked48089 : (cuts48089.take 1).map (fun c => (6307053569-1+2*2^10*c.k,111171521483134+c.lower,111171908328240+c.upper)) = pointBounds48089 := by
 decide +kernel
def cuts48090 : List PrefixCut := [⟨63,261917074,261917217⟩,
⟨64,265754974,265755119⟩]
theorem checked48090 : checkPrefixCuts (2^48) 6307184641 10 Manual.Count131072.C048090.packed 64 cuts48090 = true := by
 decide +kernel
def pointBounds48090 : List (Nat × Nat × Nat) := [(6307313664,111172042689598,111172429535003)]
theorem point_links_checked48090 : (cuts48090.take 1).map (fun c => (6307184641-1+2*2^10*c.k,111171780772524+c.lower,111172167617786+c.upper)) = pointBounds48090 := by
 decide +kernel
def cuts48091 : List PrefixCut := [⟨64,254905261,254905405⟩]
theorem checked48091 : checkPrefixCuts (2^48) 6307315713 10 Manual.Count131072.C048091.packed 64 cuts48091 = true := by
 decide +kernel
def cuts48092 : List PrefixCut := [⟨32,129057160,129057232⟩,
⟨64,260031855,260032000⟩]
theorem checked48092 : checkPrefixCuts (2^48) 6307446785 10 Manual.Count131072.C048092.packed 64 cuts48092 = true := by
 decide +kernel
def pointBounds48092 : List (Nat × Nat × Nat) := [(6307512320,111172430489919,111172817335542)]
theorem point_links_checked48092 : (cuts48092.take 1).map (fun c => (6307446785-1+2*2^10*c.k,111172301432759+c.lower,111172688278310+c.upper)) = pointBounds48092 := by
 decide +kernel
def cuts48093 : List PrefixCut := [⟨64,256724272,256724417⟩]
theorem checked48093 : checkPrefixCuts (2^48) 6307577857 10 Manual.Count131072.C048093.packed 64 cuts48093 = true := by
 decide +kernel
def cuts48094 : List PrefixCut := [⟨1,4551642,4551645⟩,
⟨64,258860866,258861018⟩]
theorem checked48094 : checkPrefixCuts (2^48) 6307708929 10 Manual.Count131072.C048094.packed 64 cuts48094 = true := by
 decide +kernel
def pointBounds48094 : List (Nat × Nat × Nat) := [(6307710976,111172822740528,111173209586372)]
theorem point_links_checked48094 : (cuts48094.take 1).map (fun c => (6307708929-1+2*2^10*c.k,111172818188886+c.lower,111173205034727+c.upper)) = pointBounds48094 := by
 decide +kernel
def cuts48095 : List PrefixCut := [⟨34,139580054,139580131⟩,
⟨64,260372658,260372803⟩]
theorem checked48095 : checkPrefixCuts (2^48) 6307840001 10 Manual.Count131072.C048095.packed 64 cuts48095 = true := by
 decide +kernel
def pointBounds48095 : List (Nat × Nat × Nat) := [(6307909632,111173216629806,111173603475876)]
theorem point_links_checked48095 : (cuts48095.take 1).map (fun c => (6307840001-1+2*2^10*c.k,111173077049752+c.lower,111173463895745+c.upper)) = pointBounds48095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000252
