import PlattAssemblyKernel
import PlattCertificates.Count131072.C050896
import PlattCertificates.Count131072.C050897
import PlattCertificates.Count131072.C050898
import PlattCertificates.Count131072.C050899
import PlattCertificates.Count131072.C050900
import PlattCertificates.Count131072.C050901
import PlattCertificates.Count131072.C050902
import PlattCertificates.Count131072.C050903
import PlattCertificates.Count131072.C050904
import PlattCertificates.Count131072.C050905
import PlattCertificates.Count131072.C050906
import PlattCertificates.Count131072.C050907
import PlattCertificates.Count131072.C050908
import PlattCertificates.Count131072.C050909
import PlattCertificates.Count131072.C050910
import PlattCertificates.Count131072.C050911
import PlattCertificates.Count131072.C050912
import PlattCertificates.Count131072.C050913
import PlattCertificates.Count131072.C050914
import PlattCertificates.Count131072.C050915
import PlattCertificates.Count131072.C050916
import PlattCertificates.Count131072.C050917
import PlattCertificates.Count131072.C050918
import PlattCertificates.Count131072.C050919
import PlattCertificates.Count131072.C050920
import PlattCertificates.Count131072.C050921
import PlattCertificates.Count131072.C050922
import PlattCertificates.Count131072.C050923
import PlattCertificates.Count131072.C050924
import PlattCertificates.Count131072.C050925
import PlattCertificates.Count131072.C050926
import PlattCertificates.Count131072.C050927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50896 : List PrefixCut := [⟨64,244449545,244449684⟩]
theorem checked50896 : checkPrefixCuts (2^48) 6674972673 10 Manual.Count131072.C050896.packed 64 cuts50896 = true := by
 decide +kernel
def cuts50897 : List PrefixCut := [⟨38,146574656,146574744⟩,
⟨64,246763945,246764089⟩]
theorem checked50897 : checkPrefixCuts (2^48) 6675103745 10 Manual.Count131072.C050897.packed 64 cuts50897 = true := by
 decide +kernel
def pointBounds50897 : List (Nat × Nat × Nat) := [(6675181568,111878216204007,111878603452017)]
theorem point_links_checked50897 : (cuts50897.take 1).map (fun c => (6675103745-1+2*2^10*c.k,111878069629351+c.lower,111878456877273+c.upper)) = pointBounds50897 := by
 decide +kernel
def cuts50898 : List PrefixCut := [⟨64,245747083,245747220⟩]
theorem checked50898 : checkPrefixCuts (2^48) 6675234817 10 Manual.Count131072.C050898.packed 64 cuts50898 = true := by
 decide +kernel
def cuts50899 : List PrefixCut := [⟨12,45159930,45159956⟩,
⟨64,245953091,245953228⟩]
theorem checked50899 : checkPrefixCuts (2^48) 6675365889 10 Manual.Count131072.C050899.packed 64 cuts50899 = true := by
 decide +kernel
def pointBounds50899 : List (Nat × Nat × Nat) := [(6675390464,111878607300309,111878994548538)]
theorem point_links_checked50899 : (cuts50899.take 1).map (fun c => (6675365889-1+2*2^10*c.k,111878562140379+c.lower,111878949388582+c.upper)) = pointBounds50899 := by
 decide +kernel
def cuts50900 : List PrefixCut := [⟨50,188519984,188520093⟩,
⟨64,242153414,242153554⟩]
theorem checked50900 : checkPrefixCuts (2^48) 6675496961 10 Manual.Count131072.C050900.packed 64 cuts50900 = true := by
 decide +kernel
def pointBounds50900 : List (Nat × Nat × Nat) := [(6675599360,111878996613454,111879383861903)]
theorem point_links_checked50900 : (cuts50900.take 1).map (fun c => (6675496961-1+2*2^10*c.k,111878808093470+c.lower,111879195341810+c.upper)) = pointBounds50900 := by
 decide +kernel
def cuts50901 : List PrefixCut := [⟨64,242401625,242401763⟩]
theorem checked50901 : checkPrefixCuts (2^48) 6675628033 10 Manual.Count131072.C050901.packed 64 cuts50901 = true := by
 decide +kernel
def cuts50902 : List PrefixCut := [⟨24,90988994,90989046⟩,
⟨64,243324480,243324619⟩]
theorem checked50902 : checkPrefixCuts (2^48) 6675759105 10 Manual.Count131072.C050902.packed 64 cuts50902 = true := by
 decide +kernel
def pointBounds50902 : List (Nat × Nat × Nat) := [(6675808256,111879383637503,111879770886173)]
theorem point_links_checked50902 : (cuts50902.take 1).map (fun c => (6675759105-1+2*2^10*c.k,111879292648509+c.lower,111879679897127+c.upper)) = pointBounds50902 := by
 decide +kernel
def cuts50903 : List PrefixCut := [⟨62,234254854,234254986⟩,
⟨64,242181327,242181463⟩]
theorem checked50903 : checkPrefixCuts (2^48) 6675890177 10 Manual.Count131072.C050903.packed 64 cuts50903 = true := by
 decide +kernel
def pointBounds50903 : List (Nat × Nat × Nat) := [(6676017152,111879770227843,111880157476732)]
theorem point_links_checked50903 : (cuts50903.take 1).map (fun c => (6675890177-1+2*2^10*c.k,111879535972989+c.lower,111879923221746+c.upper)) = pointBounds50903 := by
 decide +kernel
def cuts50904 : List PrefixCut := [⟨64,247362440,247362580⟩]
theorem checked50904 : checkPrefixCuts (2^48) 6676021249 10 Manual.Count131072.C050904.packed 64 cuts50904 = true := by
 decide +kernel
def cuts50905 : List PrefixCut := [⟨36,135927100,135927177⟩,
⟨64,243858234,243858372⟩]
theorem checked50905 : checkPrefixCuts (2^48) 6676152321 10 Manual.Count131072.C050905.packed 64 cuts50905 = true := by
 decide +kernel
def pointBounds50905 : List (Nat × Nat × Nat) := [(6676226048,111880161443856,111880548692966)]
theorem point_links_checked50905 : (cuts50905.take 1).map (fun c => (6676152321-1+2*2^10*c.k,111880025516756+c.lower,111880412765789+c.upper)) = pointBounds50905 := by
 decide +kernel
def cuts50906 : List PrefixCut := [⟨64,248491060,248491202⟩]
theorem checked50906 : checkPrefixCuts (2^48) 6676283393 10 Manual.Count131072.C050906.packed 64 cuts50906 = true := by
 decide +kernel
def cuts50907 : List PrefixCut := [⟨10,39124041,39124063⟩,
⟨64,242626063,242626201⟩]
theorem checked50907 : checkPrefixCuts (2^48) 6676414465 10 Manual.Count131072.C050907.packed 64 cuts50907 = true := by
 decide +kernel
def pointBounds50907 : List (Nat × Nat × Nat) := [(6676434944,111880556990091,111880944239426)]
theorem point_links_checked50907 : (cuts50907.take 1).map (fun c => (6676414465-1+2*2^10*c.k,111880517866050+c.lower,111880905115363+c.upper)) = pointBounds50907 := by
 decide +kernel
def cuts50908 : List PrefixCut := [⟨48,185412880,185412984⟩,
⟨64,243338024,243338161⟩]
theorem checked50908 : checkPrefixCuts (2^48) 6676545537 10 Manual.Count131072.C050908.packed 64 cuts50908 = true := by
 decide +kernel
def pointBounds50908 : List (Nat × Nat × Nat) := [(6676643840,111880945904993,111881333154548)]
theorem point_links_checked50908 : (cuts50908.take 1).map (fun c => (6676545537-1+2*2^10*c.k,111880760492113+c.lower,111881147741564+c.upper)) = pointBounds50908 := by
 decide +kernel
def cuts50909 : List PrefixCut := [⟨64,243543983,243544130⟩]
theorem checked50909 : checkPrefixCuts (2^48) 6676676609 10 Manual.Count131072.C050909.packed 64 cuts50909 = true := by
 decide +kernel
def cuts50910 : List PrefixCut := [⟨22,85494324,85494375⟩,
⟨64,247206847,247206990⟩]
theorem checked50910 : checkPrefixCuts (2^48) 6676807681 10 Manual.Count131072.C050910.packed 64 cuts50910 = true := by
 decide +kernel
def pointBounds50910 : List (Nat × Nat × Nat) := [(6676852736,111881332868444,111881720118230)]
theorem point_links_checked50910 : (cuts50910.take 1).map (fun c => (6676807681-1+2*2^10*c.k,111881247374120+c.lower,111881634623855+c.upper)) = pointBounds50910 := by
 decide +kernel
def cuts50911 : List PrefixCut := [⟨60,228527082,228527209⟩,
⟨64,243829520,243829655⟩]
theorem checked50911 : checkPrefixCuts (2^48) 6676938753 10 Manual.Count131072.C050911.packed 64 cuts50911 = true := by
 decide +kernel
def pointBounds50911 : List (Nat × Nat × Nat) := [(6677061632,111881723108049,111882110358054)]
theorem point_links_checked50911 : (cuts50911.take 1).map (fun c => (6676938753-1+2*2^10*c.k,111881494580967+c.lower,111881881830845+c.upper)) = pointBounds50911 := by
 decide +kernel
def cuts50912 : List PrefixCut := [⟨64,247745158,247745293⟩]
theorem checked50912 : checkPrefixCuts (2^48) 6677069825 10 Manual.Count131072.C050912.packed 64 cuts50912 = true := by
 decide +kernel
def cuts50913 : List PrefixCut := [⟨34,128191541,128191617⟩,
⟨64,244494406,244494548⟩]
theorem checked50913 : checkPrefixCuts (2^48) 6677200897 10 Manual.Count131072.C050913.packed 64 cuts50913 = true := by
 decide +kernel
def pointBounds50913 : List (Nat × Nat × Nat) := [(6677270528,111882114347186,111882501597410)]
theorem point_links_checked50913 : (cuts50913.take 1).map (fun c => (6677200897-1+2*2^10*c.k,111881986155645+c.lower,111882373405793+c.upper)) = pointBounds50913 := by
 decide +kernel
def cuts50914 : List PrefixCut := [⟨64,243604393,243604533⟩]
theorem checked50914 : checkPrefixCuts (2^48) 6677331969 10 Manual.Count131072.C050914.packed 64 cuts50914 = true := by
 decide +kernel
def cuts50915 : List PrefixCut := [⟨8,30181489,30181507⟩,
⟨64,244400529,244400668⟩]
theorem checked50915 : checkPrefixCuts (2^48) 6677463041 10 Manual.Count131072.C050915.packed 64 cuts50915 = true := by
 decide +kernel
def pointBounds50915 : List (Nat × Nat × Nat) := [(6677479424,111882504435933,111882891686381)]
theorem point_links_checked50915 : (cuts50915.take 1).map (fun c => (6677463041-1+2*2^10*c.k,111882474254444+c.lower,111882861504874+c.upper)) = pointBounds50915 := by
 decide +kernel
def cuts50916 : List PrefixCut := [⟨46,178639517,178639615⟩,
⟨64,245280931,245281067⟩]
theorem checked50916 : checkPrefixCuts (2^48) 6677594113 10 Manual.Count131072.C050916.packed 64 cuts50916 = true := by
 decide +kernel
def pointBounds50916 : List (Nat × Nat × Nat) := [(6677688320,111882897294490,111883284545157)]
theorem point_links_checked50916 : (cuts50916.take 1).map (fun c => (6677594113-1+2*2^10*c.k,111882718654973+c.lower,111883105905542+c.upper)) = pointBounds50916 := by
 decide +kernel
def cuts50917 : List PrefixCut := [⟨64,241566821,241566955⟩]
theorem checked50917 : checkPrefixCuts (2^48) 6677725185 10 Manual.Count131072.C050917.packed 64 cuts50917 = true := by
 decide +kernel
def cuts50918 : List PrefixCut := [⟨20,78231066,78231108⟩,
⟨64,248769742,248769879⟩]
theorem checked50918 : checkPrefixCuts (2^48) 6677856257 10 Manual.Count131072.C050918.packed 64 cuts50918 = true := by
 decide +kernel
def pointBounds50918 : List (Nat × Nat × Nat) := [(6677897216,111883283733791,111883670984672)]
theorem point_links_checked50918 : (cuts50918.take 1).map (fun c => (6677856257-1+2*2^10*c.k,111883205502725+c.lower,111883592753564+c.upper)) = pointBounds50918 := by
 decide +kernel
def cuts50919 : List PrefixCut := [⟨58,221452341,221452463⟩,
⟨64,243959838,243959974⟩]
theorem checked50919 : checkPrefixCuts (2^48) 6677987329 10 Manual.Count131072.C050919.packed 64 cuts50919 = true := by
 decide +kernel
def pointBounds50919 : List (Nat × Nat × Nat) := [(6678106112,111883675724808,111884062975906)]
theorem point_links_checked50919 : (cuts50919.take 1).map (fun c => (6677987329-1+2*2^10*c.k,111883454272467+c.lower,111883841523443+c.upper)) = pointBounds50919 := by
 decide +kernel
def cuts50920 : List PrefixCut := [⟨64,244629441,244629578⟩]
theorem checked50920 : checkPrefixCuts (2^48) 6678118401 10 Manual.Count131072.C050920.packed 64 cuts50920 = true := by
 decide +kernel
def cuts50921 : List PrefixCut := [⟨32,119025383,119025452⟩,
⟨64,240704881,240705021⟩]
theorem checked50921 : checkPrefixCuts (2^48) 6678249473 10 Manual.Count131072.C050921.packed 64 cuts50921 = true := by
 decide +kernel
def pointBounds50921 : List (Nat × Nat × Nat) := [(6678315008,111884061887129,111884449138447)]
theorem point_links_checked50921 : (cuts50921.take 1).map (fun c => (6678249473-1+2*2^10*c.k,111883942861746+c.lower,111884330112995+c.upper)) = pointBounds50921 := by
 decide +kernel
def cuts50922 : List PrefixCut := [⟨64,239309342,239309482⟩]
theorem checked50922 : checkPrefixCuts (2^48) 6678380545 10 Manual.Count131072.C050922.packed 64 cuts50922 = true := by
 decide +kernel
def cuts50923 : List PrefixCut := [⟨6,22506131,22506145⟩,
⟨64,244615013,244615156⟩]
theorem checked50923 : checkPrefixCuts (2^48) 6678511617 10 Manual.Count131072.C050923.packed 64 cuts50923 = true := by
 decide +kernel
def pointBounds50923 : List (Nat × Nat × Nat) := [(6678523904,111884445382100,111884832633643)]
theorem point_links_checked50923 : (cuts50923.take 1).map (fun c => (6678511617-1+2*2^10*c.k,111884422875969+c.lower,111884810127498+c.upper)) = pointBounds50923 := by
 decide +kernel
def cuts50924 : List PrefixCut := [⟨44,170140334,170140428⟩,
⟨64,246169596,246169733⟩]
theorem checked50924 : checkPrefixCuts (2^48) 6678642689 10 Manual.Count131072.C050924.packed 64 cuts50924 = true := by
 decide +kernel
def pointBounds50924 : List (Nat × Nat × Nat) := [(6678732800,111884837631316,111885224883082)]
theorem point_links_checked50924 : (cuts50924.take 1).map (fun c => (6678642689-1+2*2^10*c.k,111884667490982+c.lower,111885054742654+c.upper)) = pointBounds50924 := by
 decide +kernel
def cuts50925 : List PrefixCut := [⟨64,243636107,243636249⟩]
theorem checked50925 : checkPrefixCuts (2^48) 6678773761 10 Manual.Count131072.C050925.packed 64 cuts50925 = true := by
 decide +kernel
def cuts50926 : List PrefixCut := [⟨18,68905036,68905074⟩,
⟨64,244895618,244895753⟩]
theorem checked50926 : checkPrefixCuts (2^48) 6678904833 10 Manual.Count131072.C050926.packed 64 cuts50926 = true := by
 decide +kernel
def pointBounds50926 : List (Nat × Nat × Nat) := [(6678941696,111885226201721,111885613453710)]
theorem point_links_checked50926 : (cuts50926.take 1).map (fun c => (6678904833-1+2*2^10*c.k,111885157296685+c.lower,111885544548636+c.upper)) = pointBounds50926 := by
 decide +kernel
def cuts50927 : List PrefixCut := [⟨56,212399100,212399223⟩,
⟨64,243584379,243584520⟩]
theorem checked50927 : checkPrefixCuts (2^48) 6679035905 10 Manual.Count131072.C050927.packed 64 cuts50927 = true := by
 decide +kernel
def pointBounds50927 : List (Nat × Nat × Nat) := [(6679150592,111885614591403,111886001843612)]
theorem point_links_checked50927 : (cuts50927.take 1).map (fun c => (6679035905-1+2*2^10*c.k,111885402192303+c.lower,111885789444389+c.upper)) = pointBounds50927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000028
