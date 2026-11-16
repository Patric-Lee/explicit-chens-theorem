import PlattAssemblyKernel
import PlattCertificates.Count131072.C071824
import PlattCertificates.Count131072.C071825
import PlattCertificates.Count131072.C071826
import PlattCertificates.Count131072.C071827
import PlattCertificates.Count131072.C071828
import PlattCertificates.Count131072.C071829
import PlattCertificates.Count131072.C071830
import PlattCertificates.Count131072.C071831
import PlattCertificates.Count131072.C071832
import PlattCertificates.Count131072.C071833
import PlattCertificates.Count131072.C071834
import PlattCertificates.Count131072.C071835
import PlattCertificates.Count131072.C071836
import PlattCertificates.Count131072.C071837
import PlattCertificates.Count131072.C071838
import PlattCertificates.Count131072.C071839
import PlattCertificates.Count131072.C071840
import PlattCertificates.Count131072.C071841
import PlattCertificates.Count131072.C071842
import PlattCertificates.Count131072.C071843
import PlattCertificates.Count131072.C071844
import PlattCertificates.Count131072.C071845
import PlattCertificates.Count131072.C071846
import PlattCertificates.Count131072.C071847
import PlattCertificates.Count131072.C071848
import PlattCertificates.Count131072.C071849
import PlattCertificates.Count131072.C071850
import PlattCertificates.Count131072.C071851
import PlattCertificates.Count131072.C071852
import PlattCertificates.Count131072.C071853
import PlattCertificates.Count131072.C071854
import PlattCertificates.Count131072.C071855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71824 : List PrefixCut := [⟨64,172445393,172445495⟩]
theorem checked71824 : checkPrefixCuts (2^48) 9418047489 10 Manual.Count131072.C071824.packed 64 cuts71824 = true := by
 decide +kernel
def cuts71825 : List PrefixCut := [⟨64,169962432,169962533⟩]
theorem checked71825 : checkPrefixCuts (2^48) 9418178561 10 Manual.Count131072.C071825.packed 64 cuts71825 = true := by
 decide +kernel
def cuts71826 : List PrefixCut := [⟨14,36759631,36759652⟩,
⟨64,170468121,170468223⟩]
theorem checked71826 : checkPrefixCuts (2^48) 9418309633 10 Manual.Count131072.C071826.packed 64 cuts71826 = true := by
 decide +kernel
def pointBounds71826 : List (Nat × Nat × Nat) := [(9418338304,116129459916147,116129849607779)]
theorem point_links_checked71826 : (cuts71826.take 1).map (fun c => (9418309633-1+2*2^10*c.k,116129423156516+c.lower,116129812848127+c.upper)) = pointBounds71826 := by
 decide +kernel
def cuts71827 : List PrefixCut := [⟨64,171840488,171840587⟩]
theorem checked71827 : checkPrefixCuts (2^48) 9418440705 10 Manual.Count131072.C071827.packed 64 cuts71827 = true := by
 decide +kernel
def cuts71828 : List PrefixCut := [⟨30,80450407,80450454⟩,
⟨64,171628892,171628991⟩]
theorem checked71828 : checkPrefixCuts (2^48) 9418571777 10 Manual.Count131072.C071828.packed 64 cuts71828 = true := by
 decide +kernel
def pointBounds71828 : List (Nat × Nat × Nat) := [(9418633216,116129845915532,116130235607391)]
theorem point_links_checked71828 : (cuts71828.take 1).map (fun c => (9418571777-1+2*2^10*c.k,116129765465125+c.lower,116130155156937+c.upper)) = pointBounds71828 := by
 decide +kernel
def cuts71829 : List PrefixCut := [⟨64,172762123,172762220⟩]
theorem checked71829 : checkPrefixCuts (2^48) 9418702849 10 Manual.Count131072.C071829.packed 64 cuts71829 = true := by
 decide +kernel
def cuts71830 : List PrefixCut := [⟨46,120941001,120941075⟩,
⟨64,168217336,168217442⟩]
theorem checked71830 : checkPrefixCuts (2^48) 9418833921 10 Manual.Count131072.C071830.packed 64 cuts71830 = true := by
 decide +kernel
def pointBounds71830 : List (Nat × Nat × Nat) := [(9418928128,116130230797141,116130620489223)]
theorem point_links_checked71830 : (cuts71830.take 1).map (fun c => (9418833921-1+2*2^10*c.k,116130109856140+c.lower,116130499548148+c.upper)) = pointBounds71830 := by
 decide +kernel
def cuts71831 : List PrefixCut := [⟨64,170037895,170038003⟩]
theorem checked71831 : checkPrefixCuts (2^48) 9418964993 10 Manual.Count131072.C071831.packed 64 cuts71831 = true := by
 decide +kernel
def cuts71832 : List PrefixCut := [⟨62,165702510,165702615⟩,
⟨64,170872272,170872381⟩]
theorem checked71832 : checkPrefixCuts (2^48) 9419096065 10 Manual.Count131072.C071832.packed 64 cuts71832 = true := by
 decide +kernel
def pointBounds71832 : List (Nat × Nat × Nat) := [(9419223040,116130613813881,116131003506208)]
theorem point_links_checked71832 : (cuts71832.take 1).map (fun c => (9419096065-1+2*2^10*c.k,116130448111371+c.lower,116130837803593+c.upper)) = pointBounds71832 := by
 decide +kernel
def cuts71833 : List PrefixCut := [⟨64,170302121,170302217⟩]
theorem checked71833 : checkPrefixCuts (2^48) 9419227137 10 Manual.Count131072.C071833.packed 64 cuts71833 = true := by
 decide +kernel
def cuts71834 : List PrefixCut := [⟨64,171196208,171196312⟩]
theorem checked71834 : checkPrefixCuts (2^48) 9419358209 10 Manual.Count131072.C071834.packed 64 cuts71834 = true := by
 decide +kernel
def cuts71835 : List PrefixCut := [⟨14,36276911,36276937⟩,
⟨64,170237603,170237708⟩]
theorem checked71835 : checkPrefixCuts (2^48) 9419489281 10 Manual.Count131072.C071835.packed 64 cuts71835 = true := by
 decide +kernel
def pointBounds71835 : List (Nat × Nat × Nat) := [(9419517952,116130996758883,116131386451440)]
theorem point_links_checked71835 : (cuts71835.take 1).map (fun c => (9419489281-1+2*2^10*c.k,116130960481972+c.lower,116131350174503+c.upper)) = pointBounds71835 := by
 decide +kernel
def cuts71836 : List PrefixCut := [⟨64,170952392,170952497⟩]
theorem checked71836 : checkPrefixCuts (2^48) 9419620353 10 Manual.Count131072.C071836.packed 64 cuts71836 = true := by
 decide +kernel
def cuts71837 : List PrefixCut := [⟨30,80470216,80470266⟩,
⟨64,169216921,169217024⟩]
theorem checked71837 : checkPrefixCuts (2^48) 9419751425 10 Manual.Count131072.C071837.packed 64 cuts71837 = true := by
 decide +kernel
def pointBounds71837 : List (Nat × Nat × Nat) := [(9419812864,116131382142183,116131771834974)]
theorem point_links_checked71837 : (cuts71837.take 1).map (fun c => (9419751425-1+2*2^10*c.k,116131301671967+c.lower,116131691364708+c.upper)) = pointBounds71837 := by
 decide +kernel
def cuts71838 : List PrefixCut := [⟨64,170469536,170469641⟩]
theorem checked71838 : checkPrefixCuts (2^48) 9419882497 10 Manual.Count131072.C071838.packed 64 cuts71838 = true := by
 decide +kernel
def cuts71839 : List PrefixCut := [⟨46,122838201,122838273⟩,
⟨64,169959218,169959318⟩]
theorem checked71839 : checkPrefixCuts (2^48) 9420013569 10 Manual.Count131072.C071839.packed 64 cuts71839 = true := by
 decide +kernel
def pointBounds71839 : List (Nat × Nat × Nat) := [(9420107776,116131764196625,116132153889646)]
theorem point_links_checked71839 : (cuts71839.take 1).map (fun c => (9420013569-1+2*2^10*c.k,116131641358424+c.lower,116132031051373+c.upper)) = pointBounds71839 := by
 decide +kernel
def cuts71840 : List PrefixCut := [⟨64,170046479,170046576⟩]
theorem checked71840 : checkPrefixCuts (2^48) 9420144641 10 Manual.Count131072.C071840.packed 64 cuts71840 = true := by
 decide +kernel
def cuts71841 : List PrefixCut := [⟨62,164157892,164157991⟩,
⟨64,170103869,170103971⟩]
theorem checked71841 : checkPrefixCuts (2^48) 9420275713 10 Manual.Count131072.C071841.packed 64 cuts71841 = true := by
 decide +kernel
def pointBounds71841 : List (Nat × Nat × Nat) := [(9420402688,116132145522013,116132535215258)]
theorem point_links_checked71841 : (cuts71841.take 1).map (fun c => (9420275713-1+2*2^10*c.k,116131981364121+c.lower,116132371057267+c.upper)) = pointBounds71841 := by
 decide +kernel
def cuts71842 : List PrefixCut := [⟨64,169563690,169563789⟩]
theorem checked71842 : checkPrefixCuts (2^48) 9420406785 10 Manual.Count131072.C071842.packed 64 cuts71842 = true := by
 decide +kernel
def cuts71843 : List PrefixCut := [⟨64,170577200,170577301⟩]
theorem checked71843 : checkPrefixCuts (2^48) 9420537857 10 Manual.Count131072.C071843.packed 64 cuts71843 = true := by
 decide +kernel
def cuts71844 : List PrefixCut := [⟨14,37407750,37407771⟩,
⟨64,170066901,170067000⟩]
theorem checked71844 : checkPrefixCuts (2^48) 9420668929 10 Manual.Count131072.C071844.packed 64 cuts71844 = true := by
 decide +kernel
def pointBounds71844 : List (Nat × Nat × Nat) := [(9420697600,116132529016630,116132918710099)]
theorem point_links_checked71844 : (cuts71844.take 1).map (fun c => (9420668929-1+2*2^10*c.k,116132491608880+c.lower,116132881302328+c.upper)) = pointBounds71844 := by
 decide +kernel
def cuts71845 : List PrefixCut := [⟨64,169855387,169855490⟩]
theorem checked71845 : checkPrefixCuts (2^48) 9420800001 10 Manual.Count131072.C071845.packed 64 cuts71845 = true := by
 decide +kernel
def cuts71846 : List PrefixCut := [⟨30,79683325,79683375⟩,
⟨64,171376769,171376875⟩]
theorem checked71846 : checkPrefixCuts (2^48) 9420931073 10 Manual.Count131072.C071846.packed 64 cuts71846 = true := by
 decide +kernel
def pointBounds71846 : List (Nat × Nat × Nat) := [(9420992512,116132911214493,116133300908193)]
theorem point_links_checked71846 : (cuts71846.take 1).map (fun c => (9420931073-1+2*2^10*c.k,116132831531168+c.lower,116133221224818+c.upper)) = pointBounds71846 := by
 decide +kernel
def cuts71847 : List PrefixCut := [⟨64,169014107,169014209⟩]
theorem checked71847 : checkPrefixCuts (2^48) 9421062145 10 Manual.Count131072.C071847.packed 64 cuts71847 = true := by
 decide +kernel
def cuts71848 : List PrefixCut := [⟨46,121388749,121388823⟩,
⟨64,170176943,170177046⟩]
theorem checked71848 : checkPrefixCuts (2^48) 9421193217 10 Manual.Count131072.C071848.packed 64 cuts71848 = true := by
 decide +kernel
def pointBounds71848 : List (Nat × Nat × Nat) := [(9421287424,116133293310793,116133683004725)]
theorem point_links_checked71848 : (cuts71848.take 1).map (fun c => (9421193217-1+2*2^10*c.k,116133171922044+c.lower,116133561615902+c.upper)) = pointBounds71848 := by
 decide +kernel
def cuts71849 : List PrefixCut := [⟨64,172982934,172983035⟩]
theorem checked71849 : checkPrefixCuts (2^48) 9421324289 10 Manual.Count131072.C071849.packed 64 cuts71849 = true := by
 decide +kernel
def cuts71850 : List PrefixCut := [⟨62,164495839,164495940⟩,
⟨64,169843560,169843665⟩]
theorem checked71850 : checkPrefixCuts (2^48) 9421455361 10 Manual.Count131072.C071850.packed 64 cuts71850 = true := by
 decide +kernel
def pointBounds71850 : List (Nat × Nat × Nat) := [(9421582336,116133679577760,116134069271923)]
theorem point_links_checked71850 : (cuts71850.take 1).map (fun c => (9421455361-1+2*2^10*c.k,116133515081921+c.lower,116133904775983+c.upper)) = pointBounds71850 := by
 decide +kernel
def cuts71851 : List PrefixCut := [⟨64,170886834,170886939⟩]
theorem checked71851 : checkPrefixCuts (2^48) 9421586433 10 Manual.Count131072.C071851.packed 64 cuts71851 = true := by
 decide +kernel
def cuts71852 : List PrefixCut := [⟨64,168823105,168823201⟩]
theorem checked71852 : checkPrefixCuts (2^48) 9421717505 10 Manual.Count131072.C071852.packed 64 cuts71852 = true := by
 decide +kernel
def cuts71853 : List PrefixCut := [⟨14,38747431,38747448⟩,
⟨64,172525201,172525299⟩]
theorem checked71853 : checkPrefixCuts (2^48) 9421848577 10 Manual.Count131072.C071853.packed 64 cuts71853 = true := by
 decide +kernel
def pointBounds71853 : List (Nat × Nat × Nat) := [(9421877248,116134063382851,116134453077236)]
theorem point_links_checked71853 : (cuts71853.take 1).map (fun c => (9421848577-1+2*2^10*c.k,116134024635420+c.lower,116134414329788+c.upper)) = pointBounds71853 := by
 decide +kernel
def cuts71854 : List PrefixCut := [⟨64,169714629,169714727⟩]
theorem checked71854 : checkPrefixCuts (2^48) 9421979649 10 Manual.Count131072.C071854.packed 64 cuts71854 = true := by
 decide +kernel
def cuts71855 : List PrefixCut := [⟨30,78568023,78568063⟩,
⟨64,168517319,168517417⟩]
theorem checked71855 : checkPrefixCuts (2^48) 9422110721 10 Manual.Count131072.C071855.packed 64 cuts71855 = true := by
 decide +kernel
def pointBounds71855 : List (Nat × Nat × Nat) := [(9422172160,116134445443273,116134835137877)]
theorem point_links_checked71855 : (cuts71855.take 1).map (fun c => (9422110721-1+2*2^10*c.k,116134366875250+c.lower,116134756569814+c.upper)) = pointBounds71855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000057
