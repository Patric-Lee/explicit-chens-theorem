import PlattAssemblyKernel
import PlattCertificates.Count131072.C073648
import PlattCertificates.Count131072.C073649
import PlattCertificates.Count131072.C073650
import PlattCertificates.Count131072.C073651
import PlattCertificates.Count131072.C073652
import PlattCertificates.Count131072.C073653
import PlattCertificates.Count131072.C073654
import PlattCertificates.Count131072.C073655
import PlattCertificates.Count131072.C073656
import PlattCertificates.Count131072.C073657
import PlattCertificates.Count131072.C073658
import PlattCertificates.Count131072.C073659
import PlattCertificates.Count131072.C073660
import PlattCertificates.Count131072.C073661
import PlattCertificates.Count131072.C073662
import PlattCertificates.Count131072.C073663
import PlattCertificates.Count131072.C073664
import PlattCertificates.Count131072.C073665
import PlattCertificates.Count131072.C073666
import PlattCertificates.Count131072.C073667
import PlattCertificates.Count131072.C073668
import PlattCertificates.Count131072.C073669
import PlattCertificates.Count131072.C073670
import PlattCertificates.Count131072.C073671
import PlattCertificates.Count131072.C073672
import PlattCertificates.Count131072.C073673
import PlattCertificates.Count131072.C073674
import PlattCertificates.Count131072.C073675
import PlattCertificates.Count131072.C073676
import PlattCertificates.Count131072.C073677
import PlattCertificates.Count131072.C073678
import PlattCertificates.Count131072.C073679
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73648 : List PrefixCut := [⟨64,164824419,164824518⟩]
theorem checked73648 : checkPrefixCuts (2^48) 9657122817 10 Manual.Count131072.C073648.packed 64 cuts73648 = true := by
 decide +kernel
def cuts73649 : List PrefixCut := [⟨18,46401096,46401123⟩,
⟨64,165550841,165550941⟩]
theorem checked73649 : checkPrefixCuts (2^48) 9657253889 10 Manual.Count131072.C073649.packed 64 cuts73649 = true := by
 decide +kernel
def pointBounds73649 : List (Nat × Nat × Nat) := [(9657290752,116436357048769,116436746923189)]
theorem point_links_checked73649 : (cuts73649.take 1).map (fun c => (9657253889-1+2*2^10*c.k,116436310647673+c.lower,116436700522066+c.upper)) = pointBounds73649 := by
 decide +kernel
def cuts73650 : List PrefixCut := [⟨64,168492336,168492433⟩]
theorem checked73650 : checkPrefixCuts (2^48) 9657384961 10 Manual.Count131072.C073650.packed 64 cuts73650 = true := by
 decide +kernel
def cuts73651 : List PrefixCut := [⟨38,99590394,99590451⟩,
⟨64,166916192,166916288⟩]
theorem checked73651 : checkPrefixCuts (2^48) 9657516033 10 Manual.Count131072.C073651.packed 64 cuts73651 = true := by
 decide +kernel
def pointBounds73651 : List (Nat × Nat × Nat) := [(9657593856,116436744281244,116437134155891)]
theorem point_links_checked73651 : (cuts73651.take 1).map (fun c => (9657516033-1+2*2^10*c.k,116436644690850+c.lower,116437034565440+c.upper)) = pointBounds73651 := by
 decide +kernel
def cuts73652 : List PrefixCut := [⟨64,166214445,166214542⟩]
theorem checked73652 : checkPrefixCuts (2^48) 9657647105 10 Manual.Count131072.C073652.packed 64 cuts73652 = true := by
 decide +kernel
def cuts73653 : List PrefixCut := [⟨58,150736446,150736538⟩,
⟨64,166911652,166911753⟩]
theorem checked73653 : checkPrefixCuts (2^48) 9657778177 10 Manual.Count131072.C073653.packed 64 cuts73653 = true := by
 decide +kernel
def pointBounds73653 : List (Nat × Nat × Nat) := [(9657896960,116437128557933,116437518432808)]
theorem point_links_checked73653 : (cuts73653.take 1).map (fun c => (9657778177-1+2*2^10*c.k,116436977821487+c.lower,116437367696270+c.upper)) = pointBounds73653 := by
 decide +kernel
def cuts73654 : List PrefixCut := [⟨64,166443085,166443178⟩]
theorem checked73654 : checkPrefixCuts (2^48) 9657909249 10 Manual.Count131072.C073654.packed 64 cuts73654 = true := by
 decide +kernel
def cuts73655 : List PrefixCut := [⟨64,166673971,166674069⟩]
theorem checked73655 : checkPrefixCuts (2^48) 9658040321 10 Manual.Count131072.C073655.packed 64 cuts73655 = true := by
 decide +kernel
def cuts73656 : List PrefixCut := [⟨14,36662729,36662747⟩,
⟨64,166467712,166467803⟩]
theorem checked73656 : checkPrefixCuts (2^48) 9658171393 10 Manual.Count131072.C073656.packed 64 cuts73656 = true := by
 decide +kernel
def pointBounds73656 : List (Nat × Nat × Nat) := [(9658200064,116437514512924,116437904388017)]
theorem point_links_checked73656 : (cuts73656.take 1).map (fun c => (9658171393-1+2*2^10*c.k,116437477850195+c.lower,116437867725270+c.upper)) = pointBounds73656 := by
 decide +kernel
def cuts73657 : List PrefixCut := [⟨64,165736885,165736979⟩]
theorem checked73657 : checkPrefixCuts (2^48) 9658302465 10 Manual.Count131072.C073657.packed 64 cuts73657 = true := by
 decide +kernel
def cuts73658 : List PrefixCut := [⟨34,89759848,89759898⟩,
⟨64,167599758,167599858⟩]
theorem checked73658 : checkPrefixCuts (2^48) 9658433537 10 Manual.Count131072.C073658.packed 64 cuts73658 = true := by
 decide +kernel
def pointBounds73658 : List (Nat × Nat × Nat) := [(9658503168,116437899814640,116438289689950)]
theorem point_links_checked73658 : (cuts73658.take 1).map (fun c => (9658433537-1+2*2^10*c.k,116437810054792+c.lower,116438199930052+c.upper)) = pointBounds73658 := by
 decide +kernel
def cuts73659 : List PrefixCut := [⟨64,165120386,165120485⟩]
theorem checked73659 : checkPrefixCuts (2^48) 9658564609 10 Manual.Count131072.C073659.packed 64 cuts73659 = true := by
 decide +kernel
def cuts73660 : List PrefixCut := [⟨54,140289380,140289461⟩,
⟨64,166196403,166196498⟩]
theorem checked73660 : checkPrefixCuts (2^48) 9658695681 10 Manual.Count131072.C073660.packed 64 cuts73660 = true := by
 decide +kernel
def pointBounds73660 : List (Nat × Nat × Nat) := [(9658806272,116438283064316,116438672939856)]
theorem point_links_checked73660 : (cuts73660.take 1).map (fun c => (9658695681-1+2*2^10*c.k,116438142774936+c.lower,116438532650395+c.upper)) = pointBounds73660 := by
 decide +kernel
def cuts73661 : List PrefixCut := [⟨64,167155803,167155903⟩]
theorem checked73661 : checkPrefixCuts (2^48) 9658826753 10 Manual.Count131072.C073661.packed 64 cuts73661 = true := by
 decide +kernel
def cuts73662 : List PrefixCut := [⟨64,166017030,166017135⟩]
theorem checked73662 : checkPrefixCuts (2^48) 9658957825 10 Manual.Count131072.C073662.packed 64 cuts73662 = true := by
 decide +kernel
def cuts73663 : List PrefixCut := [⟨10,27479873,27479889⟩,
⟨64,166539328,166539428⟩]
theorem checked73663 : checkPrefixCuts (2^48) 9659088897 10 Manual.Count131072.C073663.packed 64 cuts73663 = true := by
 decide +kernel
def pointBounds73663 : List (Nat × Nat × Nat) := [(9659109376,116438669624045,116439059499820)]
theorem point_links_checked73663 : (cuts73663.take 1).map (fun c => (9659088897-1+2*2^10*c.k,116438642144172+c.lower,116439032019931+c.upper)) = pointBounds73663 := by
 decide +kernel
def cuts73664 : List PrefixCut := [⟨64,165196608,165196709⟩]
theorem checked73664 : checkPrefixCuts (2^48) 9659219969 10 Manual.Count131072.C073664.packed 64 cuts73664 = true := by
 decide +kernel
def cuts73665 : List PrefixCut := [⟨30,78153620,78153666⟩,
⟨64,167146735,167146835⟩]
theorem checked73665 : checkPrefixCuts (2^48) 9659351041 10 Manual.Count131072.C073665.packed 64 cuts73665 = true := by
 decide +kernel
def pointBounds73665 : List (Nat × Nat × Nat) := [(9659412480,116439052033728,116439441909734)]
theorem point_links_checked73665 : (cuts73665.take 1).map (fun c => (9659351041-1+2*2^10*c.k,116438973880108+c.lower,116439363756068+c.upper)) = pointBounds73665 := by
 decide +kernel
def cuts73666 : List PrefixCut := [⟨64,167843833,167843926⟩]
theorem checked73666 : checkPrefixCuts (2^48) 9659482113 10 Manual.Count131072.C073666.packed 64 cuts73666 = true := by
 decide +kernel
def cuts73667 : List PrefixCut := [⟨50,130601890,130601963⟩,
⟨64,167113059,167113154⟩]
theorem checked73667 : checkPrefixCuts (2^48) 9659613185 10 Manual.Count131072.C073667.packed 64 cuts73667 = true := by
 decide +kernel
def pointBounds73667 : List (Nat × Nat × Nat) := [(9659715584,116439439472566,116439829348792)]
theorem point_links_checked73667 : (cuts73667.take 1).map (fun c => (9659613185-1+2*2^10*c.k,116439308870676+c.lower,116439698746829+c.upper)) = pointBounds73667 := by
 decide +kernel
def cuts73668 : List PrefixCut := [⟨64,165653860,165653955⟩]
theorem checked73668 : checkPrefixCuts (2^48) 9659744257 10 Manual.Count131072.C073668.packed 64 cuts73668 = true := by
 decide +kernel
def cuts73669 : List PrefixCut := [⟨64,166875428,166875520⟩]
theorem checked73669 : checkPrefixCuts (2^48) 9659875329 10 Manual.Count131072.C073669.packed 64 cuts73669 = true := by
 decide +kernel
def cuts73670 : List PrefixCut := [⟨6,15909429,15909440⟩,
⟨64,168155218,168155324⟩]
theorem checked73670 : checkPrefixCuts (2^48) 9660006401 10 Manual.Count131072.C073670.packed 64 cuts73670 = true := by
 decide +kernel
def pointBounds73670 : List (Nat × Nat × Nat) := [(9660018688,116439824422452,116440214298898)]
theorem point_links_checked73670 : (cuts73670.take 1).map (fun c => (9660006401-1+2*2^10*c.k,116439808513023+c.lower,116440198389458+c.upper)) = pointBounds73670 := by
 decide +kernel
def cuts73671 : List PrefixCut := [⟨64,166783470,166783567⟩]
theorem checked73671 : checkPrefixCuts (2^48) 9660137473 10 Manual.Count131072.C073671.packed 64 cuts73671 = true := by
 decide +kernel
def cuts73672 : List PrefixCut := [⟨26,67044920,67044962⟩,
⟨64,165965374,165965476⟩]
theorem checked73672 : checkPrefixCuts (2^48) 9660268545 10 Manual.Count131072.C073672.packed 64 cuts73672 = true := by
 decide +kernel
def pointBounds73672 : List (Nat × Nat × Nat) := [(9660321792,116440210496631,116440600373311)]
theorem point_links_checked73672 : (cuts73672.take 1).map (fun c => (9660268545-1+2*2^10*c.k,116440143451711+c.lower,116440533328349+c.upper)) = pointBounds73672 := by
 decide +kernel
def cuts73673 : List PrefixCut := [⟨64,163573910,163574011⟩]
theorem checked73673 : checkPrefixCuts (2^48) 9660399617 10 Manual.Count131072.C073673.packed 64 cuts73673 = true := by
 decide +kernel
def cuts73674 : List PrefixCut := [⟨46,120537475,120537549⟩,
⟨64,166427064,166427166⟩]
theorem checked73674 : checkPrefixCuts (2^48) 9660530689 10 Manual.Count131072.C073674.packed 64 cuts73674 = true := by
 decide +kernel
def pointBounds73674 : List (Nat × Nat × Nat) := [(9660624896,116440593528470,116440983405385)]
theorem point_links_checked73674 : (cuts73674.take 1).map (fun c => (9660530689-1+2*2^10*c.k,116440472990995+c.lower,116440862867836+c.upper)) = pointBounds73674 := by
 decide +kernel
def cuts73675 : List PrefixCut := [⟨64,166687020,166687119⟩]
theorem checked73675 : checkPrefixCuts (2^48) 9660661761 10 Manual.Count131072.C073675.packed 64 cuts73675 = true := by
 decide +kernel
def cuts73676 : List PrefixCut := [⟨64,168986485,168986588⟩]
theorem checked73676 : checkPrefixCuts (2^48) 9660792833 10 Manual.Count131072.C073676.packed 64 cuts73676 = true := by
 decide +kernel
def cuts73677 : List PrefixCut := [⟨2,5477454,5477457⟩,
⟨64,167760504,167760603⟩]
theorem checked73677 : checkPrefixCuts (2^48) 9660923905 10 Manual.Count131072.C073677.packed 64 cuts73677 = true := by
 decide +kernel
def pointBounds73677 : List (Nat × Nat × Nat) := [(9660928000,116440980569018,116441370446166)]
theorem point_links_checked73677 : (cuts73677.take 1).map (fun c => (9660923905-1+2*2^10*c.k,116440975091564+c.lower,116441364968709+c.upper)) = pointBounds73677 := by
 decide +kernel
def cuts73678 : List PrefixCut := [⟨64,168399187,168399289⟩]
theorem checked73678 : checkPrefixCuts (2^48) 9661054977 10 Manual.Count131072.C073678.packed 64 cuts73678 = true := by
 decide +kernel
def cuts73679 : List PrefixCut := [⟨22,56142265,56142296⟩,
⟨64,165396058,165396155⟩]
theorem checked73679 : checkPrefixCuts (2^48) 9661186049 10 Manual.Count131072.C073679.packed 64 cuts73679 = true := by
 decide +kernel
def pointBounds73679 : List (Nat × Nat × Nat) := [(9661231104,116441367393520,116441757270897)]
theorem point_links_checked73679 : (cuts73679.take 1).map (fun c => (9661186049-1+2*2^10*c.k,116441311251255+c.lower,116441701128601+c.upper)) = pointBounds73679 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000114
