import PlattAssemblyKernel
import PlattCertificates.Count131072.C050736
import PlattCertificates.Count131072.C050737
import PlattCertificates.Count131072.C050738
import PlattCertificates.Count131072.C050739
import PlattCertificates.Count131072.C050740
import PlattCertificates.Count131072.C050741
import PlattCertificates.Count131072.C050742
import PlattCertificates.Count131072.C050743
import PlattCertificates.Count131072.C050744
import PlattCertificates.Count131072.C050745
import PlattCertificates.Count131072.C050746
import PlattCertificates.Count131072.C050747
import PlattCertificates.Count131072.C050748
import PlattCertificates.Count131072.C050749
import PlattCertificates.Count131072.C050750
import PlattCertificates.Count131072.C050751
import PlattCertificates.Count131072.C050752
import PlattCertificates.Count131072.C050753
import PlattCertificates.Count131072.C050754
import PlattCertificates.Count131072.C050755
import PlattCertificates.Count131072.C050756
import PlattCertificates.Count131072.C050757
import PlattCertificates.Count131072.C050758
import PlattCertificates.Count131072.C050759
import PlattCertificates.Count131072.C050760
import PlattCertificates.Count131072.C050761
import PlattCertificates.Count131072.C050762
import PlattCertificates.Count131072.C050763
import PlattCertificates.Count131072.C050764
import PlattCertificates.Count131072.C050765
import PlattCertificates.Count131072.C050766
import PlattCertificates.Count131072.C050767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50736 : List PrefixCut := [⟨40,152919353,152919438⟩,
⟨64,244712365,244712501⟩]
theorem checked50736 : checkPrefixCuts (2^48) 6654001153 10 Manual.Count131072.C050736.packed 64 cuts50736 = true := by
 decide +kernel
def pointBounds50736 : List (Nat × Nat × Nat) := [(6654083072,111838835195153,111839222420766)]
theorem point_links_checked50736 : (cuts50736.take 1).map (fun c => (6654001153-1+2*2^10*c.k,111838682275800+c.lower,111839069501328+c.upper)) = pointBounds50736 := by
 decide +kernel
def cuts50737 : List PrefixCut := [⟨64,243776926,243777065⟩]
theorem checked50737 : checkPrefixCuts (2^48) 6654132225 10 Manual.Count131072.C050737.packed 64 cuts50737 = true := by
 decide +kernel
def cuts50738 : List PrefixCut := [⟨14,53297800,53297833⟩,
⟨64,244364301,244364441⟩]
theorem checked50738 : checkPrefixCuts (2^48) 6654263297 10 Manual.Count131072.C050738.packed 64 cuts50738 = true := by
 decide +kernel
def pointBounds50738 : List (Nat × Nat × Nat) := [(6654291968,111839224062891,111839611288727)]
theorem point_links_checked50738 : (cuts50738.take 1).map (fun c => (6654263297-1+2*2^10*c.k,111839170765091+c.lower,111839557990894+c.upper)) = pointBounds50738 := by
 decide +kernel
def cuts50739 : List PrefixCut := [⟨52,198254295,198254405⟩,
⟨64,244740176,244740314⟩]
theorem checked50739 : checkPrefixCuts (2^48) 6654394369 10 Manual.Count131072.C050739.packed 64 cuts50739 = true := by
 decide +kernel
def pointBounds50739 : List (Nat × Nat × Nat) := [(6654500864,111839613383687,111840000609740)]
theorem point_links_checked50739 : (cuts50739.take 1).map (fun c => (6654394369-1+2*2^10*c.k,111839415129392+c.lower,111839802355335+c.upper)) = pointBounds50739 := by
 decide +kernel
def cuts50740 : List PrefixCut := [⟨64,245327558,245327699⟩]
theorem checked50740 : checkPrefixCuts (2^48) 6654525441 10 Manual.Count131072.C050740.packed 64 cuts50740 = true := by
 decide +kernel
def cuts50741 : List PrefixCut := [⟨26,100286811,100286866⟩,
⟨64,245365005,245365144⟩]
theorem checked50741 : checkPrefixCuts (2^48) 6654656513 10 Manual.Count131072.C050741.packed 64 cuts50741 = true := by
 decide +kernel
def pointBounds50741 : List (Nat × Nat × Nat) := [(6654709760,111840005483937,111840392710214)]
theorem point_links_checked50741 : (cuts50741.take 1).map (fun c => (6654656513-1+2*2^10*c.k,111839905197126+c.lower,111840292423348+c.upper)) = pointBounds50741 := by
 decide +kernel
def cuts50742 : List PrefixCut := [⟨64,245317873,245318013⟩]
theorem checked50742 : checkPrefixCuts (2^48) 6654787585 10 Manual.Count131072.C050742.packed 64 cuts50742 = true := by
 decide +kernel
def pointBounds50742 : List (Nat × Nat × Nat) := [(6654918656,111840395880004,111840783106505)]
theorem point_links_checked50742 : (cuts50742.take 1).map (fun c => (6654787585-1+2*2^10*c.k,111840150562131+c.lower,111840537788492+c.upper)) = pointBounds50742 := by
 decide +kernel
def cuts50743 : List PrefixCut := [⟨64,247004853,247004990⟩]
theorem checked50743 : checkPrefixCuts (2^48) 6654918657 10 Manual.Count131072.C050743.packed 64 cuts50743 = true := by
 decide +kernel
def cuts50744 : List PrefixCut := [⟨38,146508799,146508881⟩,
⟨64,245096743,245096881⟩]
theorem checked50744 : checkPrefixCuts (2^48) 6655049729 10 Manual.Count131072.C050744.packed 64 cuts50744 = true := by
 decide +kernel
def pointBounds50744 : List (Nat × Nat × Nat) := [(6655127552,111840789393656,111841176620376)]
theorem point_links_checked50744 : (cuts50744.take 1).map (fun c => (6655049729-1+2*2^10*c.k,111840642884857+c.lower,111841030111495+c.upper)) = pointBounds50744 := by
 decide +kernel
def cuts50745 : List PrefixCut := [⟨64,246741348,246741491⟩]
theorem checked50745 : checkPrefixCuts (2^48) 6655180801 10 Manual.Count131072.C050745.packed 64 cuts50745 = true := by
 decide +kernel
def cuts50746 : List PrefixCut := [⟨12,44238675,44238700⟩,
⟨64,243353060,243353200⟩]
theorem checked50746 : checkPrefixCuts (2^48) 6655311873 10 Manual.Count131072.C050746.packed 64 cuts50746 = true := by
 decide +kernel
def pointBounds50746 : List (Nat × Nat × Nat) := [(6655336448,111841178961623,111841566188567)]
theorem point_links_checked50746 : (cuts50746.take 1).map (fun c => (6655311873-1+2*2^10*c.k,111841134722948+c.lower,111841521949867+c.upper)) = pointBounds50746 := by
 decide +kernel
def cuts50747 : List PrefixCut := [⟨50,190483672,190483781⟩,
⟨64,243728914,243729054⟩]
theorem checked50747 : checkPrefixCuts (2^48) 6655442945 10 Manual.Count131072.C050747.packed 64 cuts50747 = true := by
 decide +kernel
def pointBounds50747 : List (Nat × Nat × Nat) := [(6655545344,111841568559680,111841955786848)]
theorem point_links_checked50747 : (cuts50747.take 1).map (fun c => (6655442945-1+2*2^10*c.k,111841378076008+c.lower,111841765303067+c.upper)) = pointBounds50747 := by
 decide +kernel
def cuts50748 : List PrefixCut := [⟨64,246515344,246515487⟩]
theorem checked50748 : checkPrefixCuts (2^48) 6655574017 10 Manual.Count131072.C050748.packed 64 cuts50748 = true := by
 decide +kernel
def cuts50749 : List PrefixCut := [⟨24,93293093,93293146⟩,
⟨64,247821474,247821615⟩]
theorem checked50749 : checkPrefixCuts (2^48) 6655705089 10 Manual.Count131072.C050749.packed 64 cuts50749 = true := by
 decide +kernel
def pointBounds50749 : List (Nat × Nat × Nat) := [(6655754240,111841961613359,111842348840754)]
theorem point_links_checked50749 : (cuts50749.take 1).map (fun c => (6655705089-1+2*2^10*c.k,111841868320266+c.lower,111842255547608+c.upper)) = pointBounds50749 := by
 decide +kernel
def cuts50750 : List PrefixCut := [⟨62,236271643,236271778⟩,
⟨64,243799106,243799246⟩]
theorem checked50750 : checkPrefixCuts (2^48) 6655836161 10 Manual.Count131072.C050750.packed 64 cuts50750 = true := by
 decide +kernel
def pointBounds50750 : List (Nat × Nat × Nat) := [(6655963136,111842352413383,111842739641001)]
theorem point_links_checked50750 : (cuts50750.take 1).map (fun c => (6655836161-1+2*2^10*c.k,111842116141740+c.lower,111842503369223+c.upper)) = pointBounds50750 := by
 decide +kernel
def cuts50751 : List PrefixCut := [⟨64,244470903,244471043⟩]
theorem checked50751 : checkPrefixCuts (2^48) 6655967233 10 Manual.Count131072.C050751.packed 64 cuts50751 = true := by
 decide +kernel
def cuts50752 : List PrefixCut := [⟨36,137943579,137943657⟩,
⟨64,244888969,244889108⟩]
theorem checked50752 : checkPrefixCuts (2^48) 6656098305 10 Manual.Count131072.C050752.packed 64 cuts50752 = true := by
 decide +kernel
def pointBounds50752 : List (Nat × Nat × Nat) := [(6656172032,111842742355328,111843129583169)]
theorem point_links_checked50752 : (cuts50752.take 1).map (fun c => (6656098305-1+2*2^10*c.k,111842604411749+c.lower,111842991639512+c.upper)) = pointBounds50752 := by
 decide +kernel
def cuts50753 : List PrefixCut := [⟨64,246871657,246871795⟩]
theorem checked50753 : checkPrefixCuts (2^48) 6656229377 10 Manual.Count131072.C050753.packed 64 cuts50753 = true := by
 decide +kernel
def cuts50754 : List PrefixCut := [⟨10,38396180,38396200⟩,
⟨64,245344494,245344631⟩]
theorem checked50754 : checkPrefixCuts (2^48) 6656360449 10 Manual.Count131072.C050754.packed 64 cuts50754 = true := by
 decide +kernel
def pointBounds50754 : List (Nat × Nat × Nat) := [(6656380928,111843134568555,111843521796615)]
theorem point_links_checked50754 : (cuts50754.take 1).map (fun c => (6656360449-1+2*2^10*c.k,111843096172375+c.lower,111843483400415+c.upper)) = pointBounds50754 := by
 decide +kernel
def cuts50755 : List PrefixCut := [⟨48,186521167,186521277⟩,
⟨64,246650499,246650642⟩]
theorem checked50755 : checkPrefixCuts (2^48) 6656491521 10 Manual.Count131072.C050755.packed 64 cuts50755 = true := by
 decide +kernel
def pointBounds50755 : List (Nat × Nat × Nat) := [(6656589824,111843528038036,111843915266323)]
theorem point_links_checked50755 : (cuts50755.take 1).map (fun c => (6656491521-1+2*2^10*c.k,111843341516869+c.lower,111843728745046+c.upper)) = pointBounds50755 := by
 decide +kernel
def cuts50756 : List PrefixCut := [⟨64,242966883,242967022⟩]
theorem checked50756 : checkPrefixCuts (2^48) 6656622593 10 Manual.Count131072.C050756.packed 64 cuts50756 = true := by
 decide +kernel
def cuts50757 : List PrefixCut := [⟨22,82030894,82030941⟩,
⟨64,241947279,241947414⟩]
theorem checked50757 : checkPrefixCuts (2^48) 6656753665 10 Manual.Count131072.C050757.packed 64 cuts50757 = true := by
 decide +kernel
def pointBounds50757 : List (Nat × Nat × Nat) := [(6656798720,111843913165145,111844300393651)]
theorem point_links_checked50757 : (cuts50757.take 1).map (fun c => (6656753665-1+2*2^10*c.k,111843831134251+c.lower,111844218362710+c.upper)) = pointBounds50757 := by
 decide +kernel
def cuts50758 : List PrefixCut := [⟨60,226974525,226974652⟩,
⟨64,243506971,243507108⟩]
theorem checked50758 : checkPrefixCuts (2^48) 6656884737 10 Manual.Count131072.C050758.packed 64 cuts50758 = true := by
 decide +kernel
def pointBounds50758 : List (Nat × Nat × Nat) := [(6657007616,111844300056055,111844687284776)]
theorem point_links_checked50758 : (cuts50758.take 1).map (fun c => (6656884737-1+2*2^10*c.k,111844073081530+c.lower,111844460310124+c.upper)) = pointBounds50758 := by
 decide +kernel
def cuts50759 : List PrefixCut := [⟨64,246335101,246335241⟩]
theorem checked50759 : checkPrefixCuts (2^48) 6657015809 10 Manual.Count131072.C050759.packed 64 cuts50759 = true := by
 decide +kernel
def cuts50760 : List PrefixCut := [⟨34,129042804,129042879⟩,
⟨64,244385297,244385437⟩]
theorem checked50760 : checkPrefixCuts (2^48) 6657146881 10 Manual.Count131072.C050760.packed 64 cuts50760 = true := by
 decide +kernel
def pointBounds50760 : List (Nat × Nat × Nat) := [(6657216512,111844691966406,111845079195352)]
theorem point_links_checked50760 : (cuts50760.take 1).map (fun c => (6657146881-1+2*2^10*c.k,111844562923602+c.lower,111844950152473+c.upper)) = pointBounds50760 := by
 decide +kernel
def cuts50761 : List PrefixCut := [⟨64,248185724,248185871⟩]
theorem checked50761 : checkPrefixCuts (2^48) 6657277953 10 Manual.Count131072.C050761.packed 64 cuts50761 = true := by
 decide +kernel
def cuts50762 : List PrefixCut := [⟨8,29680485,29680502⟩,
⟨64,244967573,244967716⟩]
theorem checked50762 : checkPrefixCuts (2^48) 6657409025 10 Manual.Count131072.C050762.packed 64 cuts50762 = true := by
 decide +kernel
def pointBounds50762 : List (Nat × Nat × Nat) := [(6657425408,111845085175108,111845472404283)]
theorem point_links_checked50762 : (cuts50762.take 1).map (fun c => (6657409025-1+2*2^10*c.k,111845055494623+c.lower,111845442723781+c.upper)) = pointBounds50762 := by
 decide +kernel
def cuts50763 : List PrefixCut := [⟨46,177528742,177528842⟩,
⟨64,247161263,247161399⟩]
theorem checked50763 : checkPrefixCuts (2^48) 6657540097 10 Manual.Count131072.C050763.packed 64 cuts50763 = true := by
 decide +kernel
def pointBounds50763 : List (Nat × Nat × Nat) := [(6657634304,111845477990938,111845865220339)]
theorem point_links_checked50763 : (cuts50763.take 1).map (fun c => (6657540097-1+2*2^10*c.k,111845300462196+c.lower,111845687691497+c.upper)) = pointBounds50763 := by
 decide +kernel
def cuts50764 : List PrefixCut := [⟨64,245169340,245169473⟩]
theorem checked50764 : checkPrefixCuts (2^48) 6657671169 10 Manual.Count131072.C050764.packed 64 cuts50764 = true := by
 decide +kernel
def cuts50765 : List PrefixCut := [⟨20,77113825,77113871⟩,
⟨64,244107589,244107728⟩]
theorem checked50765 : checkPrefixCuts (2^48) 6657802241 10 Manual.Count131072.C050765.packed 64 cuts50765 = true := by
 decide +kernel
def pointBounds50765 : List (Nat × Nat × Nat) := [(6657843200,111845869906624,111846257136240)]
theorem point_links_checked50765 : (cuts50765.take 1).map (fun c => (6657802241-1+2*2^10*c.k,111845792792799+c.lower,111846180022369+c.upper)) = pointBounds50765 := by
 decide +kernel
def cuts50766 : List PrefixCut := [⟨58,222161629,222161753⟩,
⟨64,244694644,244694780⟩]
theorem checked50766 : checkPrefixCuts (2^48) 6657933313 10 Manual.Count131072.C050766.packed 64 cuts50766 = true := by
 decide +kernel
def pointBounds50766 : List (Nat × Nat × Nat) := [(6658052096,111846259062017,111846646291850)]
theorem point_links_checked50766 : (cuts50766.take 1).map (fun c => (6657933313-1+2*2^10*c.k,111846036900388+c.lower,111846424130097+c.upper)) = pointBounds50766 := by
 decide +kernel
def cuts50767 : List PrefixCut := [⟨64,246676796,246676936⟩]
theorem checked50767 : checkPrefixCuts (2^48) 6658064385 10 Manual.Count131072.C050767.packed 64 cuts50767 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000023
