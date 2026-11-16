import PlattAssemblyKernel
import PlattCertificates.Count131072.C072880
import PlattCertificates.Count131072.C072881
import PlattCertificates.Count131072.C072882
import PlattCertificates.Count131072.C072883
import PlattCertificates.Count131072.C072884
import PlattCertificates.Count131072.C072885
import PlattCertificates.Count131072.C072886
import PlattCertificates.Count131072.C072887
import PlattCertificates.Count131072.C072888
import PlattCertificates.Count131072.C072889
import PlattCertificates.Count131072.C072890
import PlattCertificates.Count131072.C072891
import PlattCertificates.Count131072.C072892
import PlattCertificates.Count131072.C072893
import PlattCertificates.Count131072.C072894
import PlattCertificates.Count131072.C072895
import PlattCertificates.Count131072.C072896
import PlattCertificates.Count131072.C072897
import PlattCertificates.Count131072.C072898
import PlattCertificates.Count131072.C072899
import PlattCertificates.Count131072.C072900
import PlattCertificates.Count131072.C072901
import PlattCertificates.Count131072.C072902
import PlattCertificates.Count131072.C072903
import PlattCertificates.Count131072.C072904
import PlattCertificates.Count131072.C072905
import PlattCertificates.Count131072.C072906
import PlattCertificates.Count131072.C072907
import PlattCertificates.Count131072.C072908
import PlattCertificates.Count131072.C072909
import PlattCertificates.Count131072.C072910
import PlattCertificates.Count131072.C072911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72880 : List PrefixCut := [⟨64,170801936,170802032⟩]
theorem checked72880 : checkPrefixCuts (2^48) 9556459521 10 Manual.Count131072.C072880.packed 64 cuts72880 = true := by
 decide +kernel
def cuts72881 : List PrefixCut := [⟨34,86710741,86710789⟩,
⟨64,167324081,167324177⟩]
theorem checked72881 : checkPrefixCuts (2^48) 9556590593 10 Manual.Count131072.C072881.packed 64 cuts72881 = true := by
 decide +kernel
def pointBounds72881 : List (Nat × Nat × Nat) := [(9556660224,116308059270103,116308449067922)]
theorem point_links_checked72881 : (cuts72881.take 1).map (fun c => (9556590593-1+2*2^10*c.k,116307972559362+c.lower,116308362357133+c.upper)) = pointBounds72881 := by
 decide +kernel
def cuts72882 : List PrefixCut := [⟨64,168264303,168264402⟩]
theorem checked72882 : checkPrefixCuts (2^48) 9556721665 10 Manual.Count131072.C072882.packed 64 cuts72882 = true := by
 decide +kernel
def cuts72883 : List PrefixCut := [⟨52,137926117,137926200⟩,
⟨64,169911325,169911428⟩]
theorem checked72883 : checkPrefixCuts (2^48) 9556852737 10 Manual.Count131072.C072883.packed 64 cuts72883 = true := by
 decide +kernel
def pointBounds72883 : List (Nat × Nat × Nat) := [(9556959232,116308446073863,116308835871912)]
theorem point_links_checked72883 : (cuts72883.take 1).map (fun c => (9556852737-1+2*2^10*c.k,116308308147746+c.lower,116308697945712+c.upper)) = pointBounds72883 := by
 decide +kernel
def cuts72884 : List PrefixCut := [⟨64,166374747,166374848⟩]
theorem checked72884 : checkPrefixCuts (2^48) 9556983809 10 Manual.Count131072.C072884.packed 64 cuts72884 = true := by
 decide +kernel
def cuts72885 : List PrefixCut := [⟨64,166048506,166048612⟩]
theorem checked72885 : checkPrefixCuts (2^48) 9557114881 10 Manual.Count131072.C072885.packed 64 cuts72885 = true := by
 decide +kernel
def cuts72886 : List PrefixCut := [⟨6,16227746,16227756⟩,
⟨64,168726284,168726387⟩]
theorem checked72886 : checkPrefixCuts (2^48) 9557245953 10 Manual.Count131072.C072886.packed 64 cuts72886 = true := by
 decide +kernel
def pointBounds72886 : List (Nat × Nat × Nat) := [(9557258240,116308826710070,116309216508356)]
theorem point_links_checked72886 : (cuts72886.take 1).map (fun c => (9557245953-1+2*2^10*c.k,116308810482324+c.lower,116309200280600+c.upper)) = pointBounds72886 := by
 decide +kernel
def cuts72887 : List PrefixCut := [⟨64,167781543,167781639⟩]
theorem checked72887 : checkPrefixCuts (2^48) 9557377025 10 Manual.Count131072.C072887.packed 64 cuts72887 = true := by
 decide +kernel
def cuts72888 : List PrefixCut := [⟨24,62553036,62553071⟩,
⟨64,168338797,168338896⟩]
theorem checked72888 : checkPrefixCuts (2^48) 9557508097 10 Manual.Count131072.C072888.packed 64 cuts72888 = true := by
 decide +kernel
def pointBounds72888 : List (Nat × Nat × Nat) := [(9557557248,116309209543187,116309599341697)]
theorem point_links_checked72888 : (cuts72888.take 1).map (fun c => (9557508097-1+2*2^10*c.k,116309146990151+c.lower,116309536788626+c.upper)) = pointBounds72888 := by
 decide +kernel
def cuts72889 : List PrefixCut := [⟨64,167953645,167953750⟩]
theorem checked72889 : checkPrefixCuts (2^48) 9557639169 10 Manual.Count131072.C072889.packed 64 cuts72889 = true := by
 decide +kernel
def cuts72890 : List PrefixCut := [⟨42,110141938,110142005⟩,
⟨64,168422528,168422629⟩]
theorem checked72890 : checkPrefixCuts (2^48) 9557770241 10 Manual.Count131072.C072890.packed 64 cuts72890 = true := by
 decide +kernel
def pointBounds72890 : List (Nat × Nat × Nat) := [(9557856256,116309593424531,116309983223277)]
theorem point_links_checked72890 : (cuts72890.take 1).map (fun c => (9557770241-1+2*2^10*c.k,116309483282593+c.lower,116309873081272+c.upper)) = pointBounds72890 := by
 decide +kernel
def cuts72891 : List PrefixCut := [⟨64,168125734,168125829⟩]
theorem checked72891 : checkPrefixCuts (2^48) 9557901313 10 Manual.Count131072.C072891.packed 64 cuts72891 = true := by
 decide +kernel
def cuts72892 : List PrefixCut := [⟨60,157934193,157934287⟩,
⟨64,167828939,167829040⟩]
theorem checked72892 : checkPrefixCuts (2^48) 9558032385 10 Manual.Count131072.C072892.packed 64 cuts72892 = true := by
 decide +kernel
def pointBounds72892 : List (Nat × Nat × Nat) := [(9558155264,116309977765048,116310367564017)]
theorem point_links_checked72892 : (cuts72892.take 1).map (fun c => (9558032385-1+2*2^10*c.k,116309819830855+c.lower,116310209629730+c.upper)) = pointBounds72892 := by
 decide +kernel
def cuts72893 : List PrefixCut := [⟨64,167002093,167002194⟩]
theorem checked72893 : checkPrefixCuts (2^48) 9558163457 10 Manual.Count131072.C072893.packed 64 cuts72893 = true := by
 decide +kernel
def cuts72894 : List PrefixCut := [⟨64,167883233,167883331⟩]
theorem checked72894 : checkPrefixCuts (2^48) 9558294529 10 Manual.Count131072.C072894.packed 64 cuts72894 = true := by
 decide +kernel
def cuts72895 : List PrefixCut := [⟨14,36603600,36603620⟩,
⟨64,167674793,167674892⟩]
theorem checked72895 : checkPrefixCuts (2^48) 9558425601 10 Manual.Count131072.C072895.packed 64 cuts72895 = true := by
 decide +kernel
def pointBounds72895 : List (Nat × Nat × Nat) := [(9558454272,116310359148720,116310748947915)]
theorem point_links_checked72895 : (cuts72895.take 1).map (fun c => (9558425601-1+2*2^10*c.k,116310322545120+c.lower,116310712344295+c.upper)) = pointBounds72895 := by
 decide +kernel
def cuts72896 : List PrefixCut := [⟨64,168438116,168438208⟩]
theorem checked72896 : checkPrefixCuts (2^48) 9558556673 10 Manual.Count131072.C072896.packed 64 cuts72896 = true := by
 decide +kernel
def cuts72897 : List PrefixCut := [⟨32,82834189,82834236⟩,
⟨64,166639552,166639646⟩]
theorem checked72897 : checkPrefixCuts (2^48) 9558687745 10 Manual.Count131072.C072897.packed 64 cuts72897 = true := by
 decide +kernel
def pointBounds72897 : List (Nat × Nat × Nat) := [(9558753280,116310741492218,116311131291631)]
theorem point_links_checked72897 : (cuts72897.take 1).map (fun c => (9558687745-1+2*2^10*c.k,116310658658029+c.lower,116311048457395+c.upper)) = pointBounds72897 := by
 decide +kernel
def cuts72898 : List PrefixCut := [⟨64,168286271,168286364⟩]
theorem checked72898 : checkPrefixCuts (2^48) 9558818817 10 Manual.Count131072.C072898.packed 64 cuts72898 = true := by
 decide +kernel
def cuts72899 : List PrefixCut := [⟨50,131506094,131506173⟩,
⟨64,170551300,170551403⟩]
theorem checked72899 : checkPrefixCuts (2^48) 9558949889 10 Manual.Count131072.C072899.packed 64 cuts72899 = true := by
 decide +kernel
def pointBounds72899 : List (Nat × Nat × Nat) := [(9559052288,116311125089946,116311514889578)]
theorem point_links_checked72899 : (cuts72899.take 1).map (fun c => (9558949889-1+2*2^10*c.k,116310993583852+c.lower,116311383383405+c.upper)) = pointBounds72899 := by
 decide +kernel
def cuts72900 : List PrefixCut := [⟨64,167457177,167457275⟩]
theorem checked72900 : checkPrefixCuts (2^48) 9559080961 10 Manual.Count131072.C072900.packed 64 cuts72900 = true := by
 decide +kernel
def cuts72901 : List PrefixCut := [⟨64,166777645,166777748⟩]
theorem checked72901 : checkPrefixCuts (2^48) 9559212033 10 Manual.Count131072.C072901.packed 64 cuts72901 = true := by
 decide +kernel
def cuts72902 : List PrefixCut := [⟨4,10187966,10187973⟩,
⟨64,167217025,167217124⟩]
theorem checked72902 : checkPrefixCuts (2^48) 9559343105 10 Manual.Count131072.C072902.packed 64 cuts72902 = true := by
 decide +kernel
def pointBounds72902 : List (Nat × Nat × Nat) := [(9559351296,116311508557940,116311898357804)]
theorem point_links_checked72902 : (cuts72902.take 1).map (fun c => (9559343105-1+2*2^10*c.k,116311498369974+c.lower,116311888169831+c.upper)) = pointBounds72902 := by
 decide +kernel
def cuts72903 : List PrefixCut := [⟨64,169158060,169158153⟩]
theorem checked72903 : checkPrefixCuts (2^48) 9559474177 10 Manual.Count131072.C072903.packed 64 cuts72903 = true := by
 decide +kernel
def cuts72904 : List PrefixCut := [⟨22,57563268,57563302⟩,
⟨64,168007429,168007531⟩]
theorem checked72904 : checkPrefixCuts (2^48) 9559605249 10 Manual.Count131072.C072904.packed 64 cuts72904 = true := by
 decide +kernel
def pointBounds72904 : List (Nat × Nat × Nat) := [(9559650304,116311892308327,116312282108410)]
theorem point_links_checked72904 : (cuts72904.take 1).map (fun c => (9559605249-1+2*2^10*c.k,116311834745059+c.lower,116312224545108+c.upper)) = pointBounds72904 := by
 decide +kernel
def cuts72905 : List PrefixCut := [⟨64,173393305,173393411⟩]
theorem checked72905 : checkPrefixCuts (2^48) 9559736321 10 Manual.Count131072.C072905.packed 64 cuts72905 = true := by
 decide +kernel
def cuts72906 : List PrefixCut := [⟨40,104965225,104965290⟩,
⟨64,168532798,168532899⟩]
theorem checked72906 : checkPrefixCuts (2^48) 9559867393 10 Manual.Count131072.C072906.packed 64 cuts72906 = true := by
 decide +kernel
def pointBounds72906 : List (Nat × Nat × Nat) := [(9559949312,116312281111018,116312670911340)]
theorem point_links_checked72906 : (cuts72906.take 1).map (fun c => (9559867393-1+2*2^10*c.k,116312176145793+c.lower,116312565946050+c.upper)) = pointBounds72906 := by
 decide +kernel
def cuts72907 : List PrefixCut := [⟨64,168059405,168059506⟩]
theorem checked72907 : checkPrefixCuts (2^48) 9559998465 10 Manual.Count131072.C072907.packed 64 cuts72907 = true := by
 decide +kernel
def cuts72908 : List PrefixCut := [⟨58,151981656,151981748⟩,
⟨64,167644904,167645005⟩]
theorem checked72908 : checkPrefixCuts (2^48) 9560129537 10 Manual.Count131072.C072908.packed 64 cuts72908 = true := by
 decide +kernel
def pointBounds72908 : List (Nat × Nat × Nat) := [(9560248320,116312664719652,116313054520203)]
theorem point_links_checked72908 : (cuts72908.take 1).map (fun c => (9560129537-1+2*2^10*c.k,116312512737996+c.lower,116312902538455+c.upper)) = pointBounds72908 := by
 decide +kernel
def cuts72909 : List PrefixCut := [⟨64,166936008,166936106⟩]
theorem checked72909 : checkPrefixCuts (2^48) 9560260609 10 Manual.Count131072.C072909.packed 64 cuts72909 = true := by
 decide +kernel
def cuts72910 : List PrefixCut := [⟨64,167434227,167434325⟩]
theorem checked72910 : checkPrefixCuts (2^48) 9560391681 10 Manual.Count131072.C072910.packed 64 cuts72910 = true := by
 decide +kernel
def cuts72911 : List PrefixCut := [⟨12,30412896,30412915⟩,
⟨64,168109071,168109171⟩]
theorem checked72911 : checkPrefixCuts (2^48) 9560522753 10 Manual.Count131072.C072911.packed 64 cuts72911 = true := by
 decide +kernel
def pointBounds72911 : List (Nat × Nat × Nat) := [(9560547328,116313045166031,116313434966806)]
theorem point_links_checked72911 : (cuts72911.take 1).map (fun c => (9560522753-1+2*2^10*c.k,116313014753135+c.lower,116313404553891+c.upper)) = pointBounds72911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000090
