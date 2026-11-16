import PlattAssemblyKernel
import PlattCertificates.Count131072.C067936
import PlattCertificates.Count131072.C067937
import PlattCertificates.Count131072.C067938
import PlattCertificates.Count131072.C067939
import PlattCertificates.Count131072.C067940
import PlattCertificates.Count131072.C067941
import PlattCertificates.Count131072.C067942
import PlattCertificates.Count131072.C067943
import PlattCertificates.Count131072.C067944
import PlattCertificates.Count131072.C067945
import PlattCertificates.Count131072.C067946
import PlattCertificates.Count131072.C067947
import PlattCertificates.Count131072.C067948
import PlattCertificates.Count131072.C067949
import PlattCertificates.Count131072.C067950
import PlattCertificates.Count131072.C067951
import PlattCertificates.Count131072.C067952
import PlattCertificates.Count131072.C067953
import PlattCertificates.Count131072.C067954
import PlattCertificates.Count131072.C067955
import PlattCertificates.Count131072.C067956
import PlattCertificates.Count131072.C067957
import PlattCertificates.Count131072.C067958
import PlattCertificates.Count131072.C067959
import PlattCertificates.Count131072.C067960
import PlattCertificates.Count131072.C067961
import PlattCertificates.Count131072.C067962
import PlattCertificates.Count131072.C067963
import PlattCertificates.Count131072.C067964
import PlattCertificates.Count131072.C067965
import PlattCertificates.Count131072.C067966
import PlattCertificates.Count131072.C067967
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000248
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67936 : List PrefixCut := [⟨64,182626022,182626131⟩]
theorem checked67936 : checkPrefixCuts (2^48) 8908439553 10 Manual.Count131072.C067936.packed 64 cuts67936 = true := by
 decide +kernel
def cuts67937 : List PrefixCut := [⟨29,80980191,80980239⟩,
⟨64,178136743,178136848⟩]
theorem checked67937 : checkPrefixCuts (2^48) 8908570625 10 Manual.Count131072.C067937.packed 64 cuts67937 = true := by
 decide +kernel
def pointBounds67937 : List (Nat × Nat × Nat) := [(8908630016,115446703969797,115447093259787)]
theorem point_links_checked67937 : (cuts67937.take 1).map (fun c => (8908570625-1+2*2^10*c.k,115446622989606+c.lower,115447012279548+c.upper)) = pointBounds67937 := by
 decide +kernel
def cuts67938 : List PrefixCut := [⟨64,181767586,181767687⟩]
theorem checked67938 : checkPrefixCuts (2^48) 8908701697 10 Manual.Count131072.C067938.packed 64 cuts67938 = true := by
 decide +kernel
def cuts67939 : List PrefixCut := [⟨37,104768695,104768756⟩,
⟨64,181922881,181922990⟩]
theorem checked67939 : checkPrefixCuts (2^48) 8908832769 10 Manual.Count131072.C067939.packed 64 cuts67939 = true := by
 decide +kernel
def pointBounds67939 : List (Nat × Nat × Nat) := [(8908908544,115447087662630,115447476952839)]
theorem point_links_checked67939 : (cuts67939.take 1).map (fun c => (8908832769-1+2*2^10*c.k,115446982893935+c.lower,115447372184083+c.upper)) = pointBounds67939 := by
 decide +kernel
def cuts67940 : List PrefixCut := [⟨64,178729178,178729284⟩]
theorem checked67940 : checkPrefixCuts (2^48) 8908963841 10 Manual.Count131072.C067940.packed 64 cuts67940 = true := by
 decide +kernel
def cuts67941 : List PrefixCut := [⟨45,124069411,124069485⟩,
⟨64,175977876,175977984⟩]
theorem checked67941 : checkPrefixCuts (2^48) 8909094913 10 Manual.Count131072.C067941.packed 64 cuts67941 = true := by
 decide +kernel
def pointBounds67941 : List (Nat × Nat × Nat) := [(8909187072,115447467615405,115447856905842)]
theorem point_links_checked67941 : (cuts67941.take 1).map (fun c => (8909094913-1+2*2^10*c.k,115447343545994+c.lower,115447732836357+c.upper)) = pointBounds67941 := by
 decide +kernel
def cuts67942 : List PrefixCut := [⟨64,182641497,182641609⟩]
theorem checked67942 : checkPrefixCuts (2^48) 8909225985 10 Manual.Count131072.C067942.packed 64 cuts67942 = true := by
 decide +kernel
def cuts67943 : List PrefixCut := [⟨53,148644996,148645081⟩,
⟨64,179921823,179921924⟩]
theorem checked67943 : checkPrefixCuts (2^48) 8909357057 10 Manual.Count131072.C067943.packed 64 cuts67943 = true := by
 decide +kernel
def pointBounds67943 : List (Nat × Nat × Nat) := [(8909465600,115447850810363,115448240101031)]
theorem point_links_checked67943 : (cuts67943.take 1).map (fun c => (8909357057-1+2*2^10*c.k,115447702165367+c.lower,115448091455950+c.upper)) = pointBounds67943 := by
 decide +kernel
def cuts67944 : List PrefixCut := [⟨64,180740577,180740679⟩]
theorem checked67944 : checkPrefixCuts (2^48) 8909488129 10 Manual.Count131072.C067944.packed 64 cuts67944 = true := by
 decide +kernel
def cuts67945 : List PrefixCut := [⟨61,173219079,173219177⟩,
⟨64,181211803,181211905⟩]
theorem checked67945 : checkPrefixCuts (2^48) 8909619201 10 Manual.Count131072.C067945.packed 64 cuts67945 = true := by
 decide +kernel
def pointBounds67945 : List (Nat × Nat × Nat) := [(8909744128,115448236046846,115448625337730)]
theorem point_links_checked67945 : (cuts67945.take 1).map (fun c => (8909619201-1+2*2^10*c.k,115448062827767+c.lower,115448452118553+c.upper)) = pointBounds67945 := by
 decide +kernel
def cuts67946 : List PrefixCut := [⟨64,183388949,183389060⟩]
theorem checked67946 : checkPrefixCuts (2^48) 8909750273 10 Manual.Count131072.C067946.packed 64 cuts67946 = true := by
 decide +kernel
def cuts67947 : List PrefixCut := [⟨64,180795779,180795880⟩]
theorem checked67947 : checkPrefixCuts (2^48) 8909881345 10 Manual.Count131072.C067947.packed 64 cuts67947 = true := by
 decide +kernel
def cuts67948 : List PrefixCut := [⟨5,14373830,14373838⟩,
⟨64,180508815,180508922⟩]
theorem checked67948 : checkPrefixCuts (2^48) 8910012417 10 Manual.Count131072.C067948.packed 64 cuts67948 = true := by
 decide +kernel
def pointBounds67948 : List (Nat × Nat × Nat) := [(8910022656,115448622598128,115449011889236)]
theorem point_links_checked67948 : (cuts67948.take 1).map (fun c => (8910012417-1+2*2^10*c.k,115448608224298+c.lower,115448997515398+c.upper)) = pointBounds67948 := by
 decide +kernel
def cuts67949 : List PrefixCut := [⟨64,178579151,178579259⟩]
theorem checked67949 : checkPrefixCuts (2^48) 8910143489 10 Manual.Count131072.C067949.packed 64 cuts67949 = true := by
 decide +kernel
def cuts67950 : List PrefixCut := [⟨13,36960155,36960176⟩,
⟨64,181324832,181324931⟩]
theorem checked67950 : checkPrefixCuts (2^48) 8910274561 10 Manual.Count131072.C067950.packed 64 cuts67950 = true := by
 decide +kernel
def pointBounds67950 : List (Nat × Nat × Nat) := [(8910301184,115449004272419,115449393563755)]
theorem point_links_checked67950 : (cuts67950.take 1).map (fun c => (8910274561-1+2*2^10*c.k,115448967312264+c.lower,115449356603579+c.upper)) = pointBounds67950 := by
 decide +kernel
def cuts67951 : List PrefixCut := [⟨64,183786121,183786226⟩]
theorem checked67951 : checkPrefixCuts (2^48) 8910405633 10 Manual.Count131072.C067951.packed 64 cuts67951 = true := by
 decide +kernel
def cuts67952 : List PrefixCut := [⟨21,60398011,60398045⟩,
⟨64,180624547,180624654⟩]
theorem checked67952 : checkPrefixCuts (2^48) 8910536705 10 Manual.Count131072.C067952.packed 64 cuts67952 = true := by
 decide +kernel
def pointBounds67952 : List (Nat × Nat × Nat) := [(8910579712,115449392821228,115449782112781)]
theorem point_links_checked67952 : (cuts67952.take 1).map (fun c => (8910536705-1+2*2^10*c.k,115449332423217+c.lower,115449721714736+c.upper)) = pointBounds67952 := by
 decide +kernel
def cuts67953 : List PrefixCut := [⟨64,178726588,178726694⟩]
theorem checked67953 : checkPrefixCuts (2^48) 8910667777 10 Manual.Count131072.C067953.packed 64 cuts67953 = true := by
 decide +kernel
def cuts67954 : List PrefixCut := [⟨29,82286637,82286684⟩,
⟨64,177397291,177397395⟩]
theorem checked67954 : checkPrefixCuts (2^48) 8910798849 10 Manual.Count131072.C067954.packed 64 cuts67954 = true := by
 decide +kernel
def pointBounds67954 : List (Nat × Nat × Nat) := [(8910858240,115449774060989,115450163352768)]
theorem point_links_checked67954 : (cuts67954.take 1).map (fun c => (8910798849-1+2*2^10*c.k,115449691774352+c.lower,115450081066084+c.upper)) = pointBounds67954 := by
 decide +kernel
def cuts67955 : List PrefixCut := [⟨64,181722129,181722231⟩]
theorem checked67955 : checkPrefixCuts (2^48) 8910929921 10 Manual.Count131072.C067955.packed 64 cuts67955 = true := by
 decide +kernel
def cuts67956 : List PrefixCut := [⟨37,105184716,105184780⟩,
⟨64,179539972,179540082⟩]
theorem checked67956 : checkPrefixCuts (2^48) 8911060993 10 Manual.Count131072.C067956.packed 64 cuts67956 = true := by
 decide +kernel
def pointBounds67956 : List (Nat × Nat × Nat) := [(8911136768,115450156078488,115450545370490)]
theorem point_links_checked67956 : (cuts67956.take 1).map (fun c => (8911060993-1+2*2^10*c.k,115450050893772+c.lower,115450440185710+c.upper)) = pointBounds67956 := by
 decide +kernel
def cuts67957 : List PrefixCut := [⟨64,179284613,179284720⟩]
theorem checked67957 : checkPrefixCuts (2^48) 8911192065 10 Manual.Count131072.C067957.packed 64 cuts67957 = true := by
 decide +kernel
def cuts67958 : List PrefixCut := [⟨45,125712448,125712523⟩,
⟨64,179218813,179218917⟩]
theorem checked67958 : checkPrefixCuts (2^48) 8911323137 10 Manual.Count131072.C067958.packed 64 cuts67958 = true := by
 decide +kernel
def pointBounds67958 : List (Nat × Nat × Nat) := [(8911415296,115450535430805,115450924723035)]
theorem point_links_checked67958 : (cuts67958.take 1).map (fun c => (8911323137-1+2*2^10*c.k,115450409718357+c.lower,115450799010512+c.upper)) = pointBounds67958 := by
 decide +kernel
def cuts67959 : List PrefixCut := [⟨64,180132156,180132266⟩]
theorem checked67959 : checkPrefixCuts (2^48) 8911454209 10 Manual.Count131072.C067959.packed 64 cuts67959 = true := by
 decide +kernel
def cuts67960 : List PrefixCut := [⟨53,150123916,150124003⟩,
⟨64,182340465,182340571⟩]
theorem checked67960 : checkPrefixCuts (2^48) 8911585281 10 Manual.Count131072.C067960.packed 64 cuts67960 = true := by
 decide +kernel
def pointBounds67960 : List (Nat × Nat × Nat) := [(8911693824,115450919193242,115451308485698)]
theorem point_links_checked67960 : (cuts67960.take 1).map (fun c => (8911585281-1+2*2^10*c.k,115450769069326+c.lower,115451158361695+c.upper)) = pointBounds67960 := by
 decide +kernel
def cuts67961 : List PrefixCut := [⟨64,179747849,179747956⟩]
theorem checked67961 : checkPrefixCuts (2^48) 8911716353 10 Manual.Count131072.C067961.packed 64 cuts67961 = true := by
 decide +kernel
def cuts67962 : List PrefixCut := [⟨61,172702011,172702110⟩,
⟨64,181071744,181071847⟩]
theorem checked67962 : checkPrefixCuts (2^48) 8911847425 10 Manual.Count131072.C067962.packed 64 cuts67962 = true := by
 decide +kernel
def pointBounds67962 : List (Nat × Nat × Nat) := [(8911972352,115451303859651,115451693152332)]
theorem point_links_checked67962 : (cuts67962.take 1).map (fun c => (8911847425-1+2*2^10*c.k,115451131157640+c.lower,115451520450222+c.upper)) = pointBounds67962 := by
 decide +kernel
def cuts67963 : List PrefixCut := [⟨64,178479212,178479312⟩]
theorem checked67963 : checkPrefixCuts (2^48) 8911978497 10 Manual.Count131072.C067963.packed 64 cuts67963 = true := by
 decide +kernel
def cuts67964 : List PrefixCut := [⟨64,179929424,179929530⟩]
theorem checked67964 : checkPrefixCuts (2^48) 8912109569 10 Manual.Count131072.C067964.packed 64 cuts67964 = true := by
 decide +kernel
def cuts67965 : List PrefixCut := [⟨5,14686066,14686075⟩,
⟨64,179042446,179042552⟩]
theorem checked67965 : checkPrefixCuts (2^48) 8912240641 10 Manual.Count131072.C067965.packed 64 cuts67965 = true := by
 decide +kernel
def pointBounds67965 : List (Nat × Nat × Nat) := [(8912250880,115451685324086,115452074616986)]
theorem point_links_checked67965 : (cuts67965.take 1).map (fun c => (8912240641-1+2*2^10*c.k,115451670638020+c.lower,115452059930911+c.upper)) = pointBounds67965 := by
 decide +kernel
def cuts67966 : List PrefixCut := [⟨64,180524193,180524306⟩]
theorem checked67966 : checkPrefixCuts (2^48) 8912371713 10 Manual.Count131072.C067966.packed 64 cuts67966 = true := by
 decide +kernel
def cuts67967 : List PrefixCut := [⟨13,35213905,35213926⟩,
⟨64,177805484,177805584⟩]
theorem checked67967 : checkPrefixCuts (2^48) 8912502785 10 Manual.Count131072.C067967.packed 64 cuts67967 = true := by
 decide +kernel
def pointBounds67967 : List (Nat × Nat × Nat) := [(8912529408,115452065418564,115452454711695)]
theorem point_links_checked67967 : (cuts67967.take 1).map (fun c => (8912502785-1+2*2^10*c.k,115452030204659+c.lower,115452419497769+c.upper)) = pointBounds67967 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000248
