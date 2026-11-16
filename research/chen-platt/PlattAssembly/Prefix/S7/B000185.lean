import PlattAssemblyKernel
import PlattCertificates.Count131072.C065920
import PlattCertificates.Count131072.C065921
import PlattCertificates.Count131072.C065922
import PlattCertificates.Count131072.C065923
import PlattCertificates.Count131072.C065924
import PlattCertificates.Count131072.C065925
import PlattCertificates.Count131072.C065926
import PlattCertificates.Count131072.C065927
import PlattCertificates.Count131072.C065928
import PlattCertificates.Count131072.C065929
import PlattCertificates.Count131072.C065930
import PlattCertificates.Count131072.C065931
import PlattCertificates.Count131072.C065932
import PlattCertificates.Count131072.C065933
import PlattCertificates.Count131072.C065934
import PlattCertificates.Count131072.C065935
import PlattCertificates.Count131072.C065936
import PlattCertificates.Count131072.C065937
import PlattCertificates.Count131072.C065938
import PlattCertificates.Count131072.C065939
import PlattCertificates.Count131072.C065940
import PlattCertificates.Count131072.C065941
import PlattCertificates.Count131072.C065942
import PlattCertificates.Count131072.C065943
import PlattCertificates.Count131072.C065944
import PlattCertificates.Count131072.C065945
import PlattCertificates.Count131072.C065946
import PlattCertificates.Count131072.C065947
import PlattCertificates.Count131072.C065948
import PlattCertificates.Count131072.C065949
import PlattCertificates.Count131072.C065950
import PlattCertificates.Count131072.C065951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65920 : List PrefixCut := [⟨64,186254895,186254999⟩]
theorem checked65920 : checkPrefixCuts (2^48) 8644198401 10 Manual.Count131072.C065920.packed 64 cuts65920 = true := by
 decide +kernel
def cuts65921 : List PrefixCut := [⟨27,79027231,79027277⟩,
⟨64,186805618,186805724⟩]
theorem checked65921 : checkPrefixCuts (2^48) 8644329473 10 Manual.Count131072.C065921.packed 64 cuts65921 = true := by
 decide +kernel
def pointBounds65921 : List (Nat × Nat × Nat) := [(8644384768,115076562507839,115076951582297)]
theorem point_links_checked65921 : (cuts65921.take 1).map (fun c => (8644329473-1+2*2^10*c.k,115076483480608+c.lower,115076872555020+c.upper)) = pointBounds65921 := by
 decide +kernel
def cuts65922 : List PrefixCut := [⟨64,187616821,187616923⟩]
theorem checked65922 : checkPrefixCuts (2^48) 8644460545 10 Manual.Count131072.C065922.packed 64 cuts65922 = true := by
 decide +kernel
def cuts65923 : List PrefixCut := [⟨31,91625781,91625834⟩,
⟨64,187776764,187776874⟩]
theorem checked65923 : checkPrefixCuts (2^48) 8644591617 10 Manual.Count131072.C065923.packed 64 cuts65923 = true := by
 decide +kernel
def pointBounds65923 : List (Nat × Nat × Nat) := [(8644655104,115076949528828,115077338603501)]
theorem point_links_checked65923 : (cuts65923.take 1).map (fun c => (8644591617-1+2*2^10*c.k,115076857903047+c.lower,115077246977667+c.upper)) = pointBounds65923 := by
 decide +kernel
def cuts65924 : List PrefixCut := [⟨64,185038862,185038975⟩]
theorem checked65924 : checkPrefixCuts (2^48) 8644722689 10 Manual.Count131072.C065924.packed 64 cuts65924 = true := by
 decide +kernel
def cuts65925 : List PrefixCut := [⟨35,103702595,103702660⟩,
⟨64,189203685,189203801⟩]
theorem checked65925 : checkPrefixCuts (2^48) 8644853761 10 Manual.Count131072.C065925.packed 64 cuts65925 = true := by
 decide +kernel
def pointBounds65925 : List (Nat × Nat × Nat) := [(8644925440,115077334421268,115077723496176)]
theorem point_links_checked65925 : (cuts65925.take 1).map (fun c => (8644853761-1+2*2^10*c.k,115077230718673+c.lower,115077619793516+c.upper)) = pointBounds65925 := by
 decide +kernel
def cuts65926 : List PrefixCut := [⟨64,185651858,185651970⟩]
theorem checked65926 : checkPrefixCuts (2^48) 8644984833 10 Manual.Count131072.C065926.packed 64 cuts65926 = true := by
 decide +kernel
def cuts65927 : List PrefixCut := [⟨39,114248420,114248483⟩,
⟨64,186495593,186495697⟩]
theorem checked65927 : checkPrefixCuts (2^48) 8645115905 10 Manual.Count131072.C065927.packed 64 cuts65927 = true := by
 decide +kernel
def pointBounds65927 : List (Nat × Nat × Nat) := [(8645195776,115077719822636,115078108897770)]
theorem point_links_checked65927 : (cuts65927.take 1).map (fun c => (8645115905-1+2*2^10*c.k,115077605574216+c.lower,115077994649287+c.upper)) = pointBounds65927 := by
 decide +kernel
def cuts65928 : List PrefixCut := [⟨64,183953229,183953340⟩]
theorem checked65928 : checkPrefixCuts (2^48) 8645246977 10 Manual.Count131072.C065928.packed 64 cuts65928 = true := by
 decide +kernel
def cuts65929 : List PrefixCut := [⟨43,126779615,126779686⟩,
⟨64,187010868,187010973⟩]
theorem checked65929 : checkPrefixCuts (2^48) 8645378049 10 Manual.Count131072.C065929.packed 64 cuts65929 = true := by
 decide +kernel
def pointBounds65929 : List (Nat × Nat × Nat) := [(8645466112,115078102802653,115078491878010)]
theorem point_links_checked65929 : (cuts65929.take 1).map (fun c => (8645378049-1+2*2^10*c.k,115077976023038+c.lower,115078365098324+c.upper)) = pointBounds65929 := by
 decide +kernel
def cuts65930 : List PrefixCut := [⟨64,185412732,185412839⟩]
theorem checked65930 : checkPrefixCuts (2^48) 8645509121 10 Manual.Count131072.C065930.packed 64 cuts65930 = true := by
 decide +kernel
def cuts65931 : List PrefixCut := [⟨47,137519408,137519491⟩,
⟨64,187656312,187656425⟩]
theorem checked65931 : checkPrefixCuts (2^48) 8645640193 10 Manual.Count131072.C065931.packed 64 cuts65931 = true := by
 decide +kernel
def pointBounds65931 : List (Nat × Nat × Nat) := [(8645736448,115078485966046,115078875041627)]
theorem point_links_checked65931 : (cuts65931.take 1).map (fun c => (8645640193-1+2*2^10*c.k,115078348446638+c.lower,115078737522136+c.upper)) = pointBounds65931 := by
 decide +kernel
def cuts65932 : List PrefixCut := [⟨64,188923171,188923281⟩]
theorem checked65932 : checkPrefixCuts (2^48) 8645771265 10 Manual.Count131072.C065932.packed 64 cuts65932 = true := by
 decide +kernel
def cuts65933 : List PrefixCut := [⟨51,147249327,147249413⟩,
⟨64,184850849,184850955⟩]
theorem checked65933 : checkPrefixCuts (2^48) 8645902337 10 Manual.Count131072.C065933.packed 64 cuts65933 = true := by
 decide +kernel
def pointBounds65933 : List (Nat × Nat × Nat) := [(8646006784,115078872275448,115079261351255)]
theorem point_links_checked65933 : (cuts65933.take 1).map (fun c => (8645902337-1+2*2^10*c.k,115078725026121+c.lower,115079114101842+c.upper)) = pointBounds65933 := by
 decide +kernel
def cuts65934 : List PrefixCut := [⟨64,189633637,189633741⟩]
theorem checked65934 : checkPrefixCuts (2^48) 8646033409 10 Manual.Count131072.C065934.packed 64 cuts65934 = true := by
 decide +kernel
def cuts65935 : List PrefixCut := [⟨55,159224908,159224997⟩,
⟨64,185952092,185952196⟩]
theorem checked65935 : checkPrefixCuts (2^48) 8646164481 10 Manual.Count131072.C065935.packed 64 cuts65935 = true := by
 decide +kernel
def pointBounds65935 : List (Nat × Nat × Nat) := [(8646277120,115079258735515,115079647811535)]
theorem point_links_checked65935 : (cuts65935.take 1).map (fun c => (8646164481-1+2*2^10*c.k,115079099510607+c.lower,115079488586538+c.upper)) = pointBounds65935 := by
 decide +kernel
def cuts65936 : List PrefixCut := [⟨64,185298190,185298298⟩]
theorem checked65936 : checkPrefixCuts (2^48) 8646295553 10 Manual.Count131072.C065936.packed 64 cuts65936 = true := by
 decide +kernel
def cuts65937 : List PrefixCut := [⟨59,170125495,170125589⟩,
⟨64,184449001,184449104⟩]
theorem checked65937 : checkPrefixCuts (2^48) 8646426625 10 Manual.Count131072.C065937.packed 64 cuts65937 = true := by
 decide +kernel
def pointBounds65937 : List (Nat × Nat × Nat) := [(8646547456,115079640886384,115080029962621)]
theorem point_links_checked65937 : (cuts65937.take 1).map (fun c => (8646426625-1+2*2^10*c.k,115079470760889+c.lower,115079859837032+c.upper)) = pointBounds65937 := by
 decide +kernel
def cuts65938 : List PrefixCut := [⟨64,186236615,186236721⟩]
theorem checked65938 : checkPrefixCuts (2^48) 8646557697 10 Manual.Count131072.C065938.packed 64 cuts65938 = true := by
 decide +kernel
def cuts65939 : List PrefixCut := [⟨63,183206418,183206522⟩,
⟨64,186233793,186233899⟩]
theorem checked65939 : checkPrefixCuts (2^48) 8646688769 10 Manual.Count131072.C065939.packed 64 cuts65939 = true := by
 decide +kernel
def pointBounds65939 : List (Nat × Nat × Nat) := [(8646817792,115080024652923,115080413729379)]
theorem point_links_checked65939 : (cuts65939.take 1).map (fun c => (8646688769-1+2*2^10*c.k,115079841446505+c.lower,115080230522857+c.upper)) = pointBounds65939 := by
 decide +kernel
def cuts65940 : List PrefixCut := [⟨64,187077337,187077446⟩]
theorem checked65940 : checkPrefixCuts (2^48) 8646819841 10 Manual.Count131072.C065940.packed 64 cuts65940 = true := by
 decide +kernel
def cuts65941 : List PrefixCut := [⟨64,185674765,185674870⟩]
theorem checked65941 : checkPrefixCuts (2^48) 8646950913 10 Manual.Count131072.C065941.packed 64 cuts65941 = true := by
 decide +kernel
def cuts65942 : List PrefixCut := [⟨3,8430817,8430823⟩,
⟨64,188992182,188992291⟩]
theorem checked65942 : checkPrefixCuts (2^48) 8647081985 10 Manual.Count131072.C065942.packed 64 cuts65942 = true := by
 decide +kernel
def pointBounds65942 : List (Nat × Nat × Nat) := [(8647088128,115080408863217,115080797939895)]
theorem point_links_checked65942 : (cuts65942.take 1).map (fun c => (8647081985-1+2*2^10*c.k,115080400432400+c.lower,115080789509072+c.upper)) = pointBounds65942 := by
 decide +kernel
def cuts65943 : List PrefixCut := [⟨64,185799348,185799451⟩]
theorem checked65943 : checkPrefixCuts (2^48) 8647213057 10 Manual.Count131072.C065943.packed 64 cuts65943 = true := by
 decide +kernel
def cuts65944 : List PrefixCut := [⟨7,20083606,20083618⟩,
⟨64,188172697,188172810⟩]
theorem checked65944 : checkPrefixCuts (2^48) 8647344129 10 Manual.Count131072.C065944.packed 64 cuts65944 = true := by
 decide +kernel
def pointBounds65944 : List (Nat × Nat × Nat) := [(8647358464,115080795307536,115081184384432)]
theorem point_links_checked65944 : (cuts65944.take 1).map (fun c => (8647344129-1+2*2^10*c.k,115080775223930+c.lower,115081164300814+c.upper)) = pointBounds65944 := by
 decide +kernel
def cuts65945 : List PrefixCut := [⟨64,188592984,188593093⟩]
theorem checked65945 : checkPrefixCuts (2^48) 8647475201 10 Manual.Count131072.C065945.packed 64 cuts65945 = true := by
 decide +kernel
def cuts65946 : List PrefixCut := [⟨11,33623545,33623565⟩,
⟨64,187190517,187190627⟩]
theorem checked65946 : checkPrefixCuts (2^48) 8647606273 10 Manual.Count131072.C065946.packed 64 cuts65946 = true := by
 decide +kernel
def pointBounds65946 : List (Nat × Nat × Nat) := [(8647628800,115081185613156,115081574690282)]
theorem point_links_checked65946 : (cuts65946.take 1).map (fun c => (8647606273-1+2*2^10*c.k,115081151989611+c.lower,115081541066717+c.upper)) = pointBounds65946 := by
 decide +kernel
def cuts65947 : List PrefixCut := [⟨64,183704968,183705073⟩]
theorem checked65947 : checkPrefixCuts (2^48) 8647737345 10 Manual.Count131072.C065947.packed 64 cuts65947 = true := by
 decide +kernel
def cuts65948 : List PrefixCut := [⟨15,43745067,43745094⟩,
⟨64,189267913,189268028⟩]
theorem checked65948 : checkPrefixCuts (2^48) 8647868417 10 Manual.Count131072.C065948.packed 64 cuts65948 = true := by
 decide +kernel
def pointBounds65948 : List (Nat × Nat × Nat) := [(8647899136,115081566630163,115081955707511)]
theorem point_links_checked65948 : (cuts65948.take 1).map (fun c => (8647868417-1+2*2^10*c.k,115081522885096+c.lower,115081911962417+c.upper)) = pointBounds65948 := by
 decide +kernel
def cuts65949 : List PrefixCut := [⟨64,185033852,185033967⟩]
theorem checked65949 : checkPrefixCuts (2^48) 8647999489 10 Manual.Count131072.C065949.packed 64 cuts65949 = true := by
 decide +kernel
def cuts65950 : List PrefixCut := [⟨19,55135315,55135347⟩,
⟨64,187797559,187797667⟩]
theorem checked65950 : checkPrefixCuts (2^48) 8648130561 10 Manual.Count131072.C065950.packed 64 cuts65950 = true := by
 decide +kernel
def pointBounds65950 : List (Nat × Nat × Nat) := [(8648169472,115081952322176,115082341399759)]
theorem point_links_checked65950 : (cuts65950.take 1).map (fun c => (8648130561-1+2*2^10*c.k,115081897186861+c.lower,115082286264412+c.upper)) = pointBounds65950 := by
 decide +kernel
def cuts65951 : List PrefixCut := [⟨64,185451350,185451458⟩]
theorem checked65951 : checkPrefixCuts (2^48) 8648261633 10 Manual.Count131072.C065951.packed 64 cuts65951 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000185
