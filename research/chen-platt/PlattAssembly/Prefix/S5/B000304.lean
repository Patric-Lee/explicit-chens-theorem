import PlattAssemblyKernel
import PlattCertificates.Count131072.C049728
import PlattCertificates.Count131072.C049729
import PlattCertificates.Count131072.C049730
import PlattCertificates.Count131072.C049731
import PlattCertificates.Count131072.C049732
import PlattCertificates.Count131072.C049733
import PlattCertificates.Count131072.C049734
import PlattCertificates.Count131072.C049735
import PlattCertificates.Count131072.C049736
import PlattCertificates.Count131072.C049737
import PlattCertificates.Count131072.C049738
import PlattCertificates.Count131072.C049739
import PlattCertificates.Count131072.C049740
import PlattCertificates.Count131072.C049741
import PlattCertificates.Count131072.C049742
import PlattCertificates.Count131072.C049743
import PlattCertificates.Count131072.C049744
import PlattCertificates.Count131072.C049745
import PlattCertificates.Count131072.C049746
import PlattCertificates.Count131072.C049747
import PlattCertificates.Count131072.C049748
import PlattCertificates.Count131072.C049749
import PlattCertificates.Count131072.C049750
import PlattCertificates.Count131072.C049751
import PlattCertificates.Count131072.C049752
import PlattCertificates.Count131072.C049753
import PlattCertificates.Count131072.C049754
import PlattCertificates.Count131072.C049755
import PlattCertificates.Count131072.C049756
import PlattCertificates.Count131072.C049757
import PlattCertificates.Count131072.C049758
import PlattCertificates.Count131072.C049759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000304
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49728 : List PrefixCut := [⟨2,7207476,7207480⟩,
⟨64,251223372,251223519⟩]
theorem checked49728 : checkPrefixCuts (2^48) 6521880577 10 Manual.Count131072.C049728.packed 64 cuts49728 = true := by
 decide +kernel
def pointBounds49728 : List (Nat × Nat × Nat) := [(6521884672,111588953582908,111589340666246)]
theorem point_links_checked49728 : (cuts49728.take 1).map (fun c => (6521880577-1+2*2^10*c.k,111588946375432+c.lower,111589333458766+c.upper)) = pointBounds49728 := by
 decide +kernel
def cuts49729 : List PrefixCut := [⟨38,149022593,149022675⟩,
⟨64,248801554,248801694⟩]
theorem checked49729 : checkPrefixCuts (2^48) 6522011649 10 Manual.Count131072.C049729.packed 64 cuts49729 = true := by
 decide +kernel
def pointBounds49729 : List (Nat × Nat × Nat) := [(6522089472,111589346621397,111589733704960)]
theorem point_links_checked49729 : (cuts49729.take 1).map (fun c => (6522011649-1+2*2^10*c.k,111589197598804+c.lower,111589584682285+c.upper)) = pointBounds49729 := by
 decide +kernel
def cuts49730 : List PrefixCut := [⟨64,252335356,252335498⟩]
theorem checked49730 : checkPrefixCuts (2^48) 6522142721 10 Manual.Count131072.C049730.packed 64 cuts49730 = true := by
 decide +kernel
def cuts49731 : List PrefixCut := [⟨10,39012913,39012936⟩,
⟨64,251682938,251683082⟩]
theorem checked49731 : checkPrefixCuts (2^48) 6522273793 10 Manual.Count131072.C049731.packed 64 cuts49731 = true := by
 decide +kernel
def pointBounds49731 : List (Nat × Nat × Nat) := [(6522294272,111589737748627,111590124832413)]
theorem point_links_checked49731 : (cuts49731.take 1).map (fun c => (6522273793-1+2*2^10*c.k,111589698735714+c.lower,111590085819477+c.upper)) = pointBounds49731 := by
 decide +kernel
def cuts49732 : List PrefixCut := [⟨46,181250023,181250125⟩,
⟨64,250728499,250728641⟩]
theorem checked49732 : checkPrefixCuts (2^48) 6522404865 10 Manual.Count131072.C049732.packed 64 cuts49732 = true := by
 decide +kernel
def pointBounds49732 : List (Nat × Nat × Nat) := [(6522499072,111590131668675,111590518752684)]
theorem point_links_checked49732 : (cuts49732.take 1).map (fun c => (6522404865-1+2*2^10*c.k,111589950418652+c.lower,111590337502559+c.upper)) = pointBounds49732 := by
 decide +kernel
def cuts49733 : List PrefixCut := [⟨64,252492768,252492908⟩]
theorem checked49733 : checkPrefixCuts (2^48) 6522535937 10 Manual.Count131072.C049733.packed 64 cuts49733 = true := by
 decide +kernel
def cuts49734 : List PrefixCut := [⟨18,70771284,70771326⟩,
⟨64,251106784,251106925⟩]
theorem checked49734 : checkPrefixCuts (2^48) 6522667009 10 Manual.Count131072.C049734.packed 64 cuts49734 = true := by
 decide +kernel
def pointBounds49734 : List (Nat × Nat × Nat) := [(6522703872,111590524411203,111590911495434)]
theorem point_links_checked49734 : (cuts49734.take 1).map (fun c => (6522667009-1+2*2^10*c.k,111590453639919+c.lower,111590840724108+c.upper)) = pointBounds49734 := by
 decide +kernel
def cuts49735 : List PrefixCut := [⟨54,210452858,210452980⟩,
⟨64,249203065,249203209⟩]
theorem checked49735 : checkPrefixCuts (2^48) 6522798081 10 Manual.Count131072.C049735.packed 64 cuts49735 = true := by
 decide +kernel
def pointBounds49735 : List (Nat × Nat × Nat) := [(6522908672,111590915199561,111591302284013)]
theorem point_links_checked49735 : (cuts49735.take 1).map (fun c => (6522798081-1+2*2^10*c.k,111590704746703+c.lower,111591091831033+c.upper)) = pointBounds49735 := by
 decide +kernel
def cuts49736 : List PrefixCut := [⟨64,250967251,250967393⟩]
theorem checked49736 : checkPrefixCuts (2^48) 6522929153 10 Manual.Count131072.C049736.packed 64 cuts49736 = true := by
 decide +kernel
def cuts49737 : List PrefixCut := [⟨26,100325075,100325131⟩,
⟨64,248890986,248891124⟩]
theorem checked49737 : checkPrefixCuts (2^48) 6523060225 10 Manual.Count131072.C049737.packed 64 cuts49737 = true := by
 decide +kernel
def pointBounds49737 : List (Nat × Nat × Nat) := [(6523113472,111591305242094,111591692326766)]
theorem point_links_checked49737 : (cuts49737.take 1).map (fun c => (6523060225-1+2*2^10*c.k,111591204917019+c.lower,111591592001635+c.upper)) = pointBounds49737 := by
 decide +kernel
def cuts49738 : List PrefixCut := [⟨62,242068467,242068607⟩,
⟨64,249705844,249705989⟩]
theorem checked49738 : checkPrefixCuts (2^48) 6523191297 10 Manual.Count131072.C049738.packed 64 cuts49738 = true := by
 decide +kernel
def pointBounds49738 : List (Nat × Nat × Nat) := [(6523318272,111591695876472,111592082961366)]
theorem point_links_checked49738 : (cuts49738.take 1).map (fun c => (6523191297-1+2*2^10*c.k,111591453808005+c.lower,111591840892759+c.upper)) = pointBounds49738 := by
 decide +kernel
def cuts49739 : List PrefixCut := [⟨64,250650061,250650205⟩]
theorem checked49739 : checkPrefixCuts (2^48) 6523322369 10 Manual.Count131072.C049739.packed 64 cuts49739 = true := by
 decide +kernel
def cuts49740 : List PrefixCut := [⟨34,130134098,130134172⟩,
⟨64,247581537,247581680⟩]
theorem checked49740 : checkPrefixCuts (2^48) 6523453441 10 Manual.Count131072.C049740.packed 64 cuts49740 = true := by
 decide +kernel
def pointBounds49740 : List (Nat × Nat × Nat) := [(6523523072,111592084298008,111592471383125)]
theorem point_links_checked49740 : (cuts49740.take 1).map (fun c => (6523453441-1+2*2^10*c.k,111591954163910+c.lower,111592341248953+c.upper)) = pointBounds49740 := by
 decide +kernel
def cuts49741 : List PrefixCut := [⟨64,247878600,247878741⟩]
theorem checked49741 : checkPrefixCuts (2^48) 6523584513 10 Manual.Count131072.C049741.packed 64 cuts49741 = true := by
 decide +kernel
def cuts49742 : List PrefixCut := [⟨6,23816795,23816809⟩,
⟨64,252360800,252360944⟩]
theorem checked49742 : checkPrefixCuts (2^48) 6523715585 10 Manual.Count131072.C049742.packed 64 cuts49742 = true := by
 decide +kernel
def pointBounds49742 : List (Nat × Nat × Nat) := [(6523727872,111592473440842,111592860526183)]
theorem point_links_checked49742 : (cuts49742.take 1).map (fun c => (6523715585-1+2*2^10*c.k,111592449624047+c.lower,111592836709374+c.upper)) = pointBounds49742 := by
 decide +kernel
def cuts49743 : List PrefixCut := [⟨42,164771745,164771839⟩,
⟨64,252269444,252269588⟩]
theorem checked49743 : checkPrefixCuts (2^48) 6523846657 10 Manual.Count131072.C049743.packed 64 cuts49743 = true := by
 decide +kernel
def pointBounds49743 : List (Nat × Nat × Nat) := [(6523932672,111592866756592,111593253842157)]
theorem point_links_checked49743 : (cuts49743.take 1).map (fun c => (6523846657-1+2*2^10*c.k,111592701984847+c.lower,111593089070318+c.upper)) = pointBounds49743 := by
 decide +kernel
def cuts49744 : List PrefixCut := [⟨64,249891446,249891588⟩]
theorem checked49744 : checkPrefixCuts (2^48) 6523977729 10 Manual.Count131072.C049744.packed 64 cuts49744 = true := by
 decide +kernel
def cuts49745 : List PrefixCut := [⟨14,57424281,57424313⟩,
⟨64,251871035,251871179⟩]
theorem checked49745 : checkPrefixCuts (2^48) 6524108801 10 Manual.Count131072.C049745.packed 64 cuts49745 = true := by
 decide +kernel
def pointBounds49745 : List (Nat × Nat × Nat) := [(6524137472,111593261570018,111593648655807)]
theorem point_links_checked49745 : (cuts49745.take 1).map (fun c => (6524108801-1+2*2^10*c.k,111593204145737+c.lower,111593591231494+c.upper)) = pointBounds49745 := by
 decide +kernel
def cuts49746 : List PrefixCut := [⟨50,195435990,195436103⟩,
⟨64,250787392,250787537⟩]
theorem checked49746 : checkPrefixCuts (2^48) 6524239873 10 Manual.Count131072.C049746.packed 64 cuts49746 = true := by
 decide +kernel
def pointBounds49746 : List (Nat × Nat × Nat) := [(6524342272,111593651452762,111594038538776)]
theorem point_links_checked49746 : (cuts49746.take 1).map (fun c => (6524239873-1+2*2^10*c.k,111593456016772+c.lower,111593843102673+c.upper)) = pointBounds49746 := by
 decide +kernel
def cuts49747 : List PrefixCut := [⟨64,249142996,249143141⟩]
theorem checked49747 : checkPrefixCuts (2^48) 6524370945 10 Manual.Count131072.C049747.packed 64 cuts49747 = true := by
 decide +kernel
def cuts49748 : List PrefixCut := [⟨22,87231222,87231270⟩,
⟨64,250345927,250346068⟩]
theorem checked49748 : checkPrefixCuts (2^48) 6524502017 10 Manual.Count131072.C049748.packed 64 cuts49748 = true := by
 decide +kernel
def pointBounds49748 : List (Nat × Nat × Nat) := [(6524547072,111594043178382,111594430264621)]
theorem point_links_checked49748 : (cuts49748.take 1).map (fun c => (6524502017-1+2*2^10*c.k,111593955947160+c.lower,111594343033351+c.upper)) = pointBounds49748 := by
 decide +kernel
def cuts49749 : List PrefixCut := [⟨58,230539868,230539999⟩,
⟨64,254352881,254353025⟩]
theorem checked49749 : checkPrefixCuts (2^48) 6524633089 10 Manual.Count131072.C049749.packed 64 cuts49749 = true := by
 decide +kernel
def pointBounds49749 : List (Nat × Nat × Nat) := [(6524751872,111594436832955,111594823919418)]
theorem point_links_checked49749 : (cuts49749.take 1).map (fun c => (6524633089-1+2*2^10*c.k,111594206293087+c.lower,111594593379419+c.upper)) = pointBounds49749 := by
 decide +kernel
def cuts49750 : List PrefixCut := [⟨64,248394573,248394715⟩]
theorem checked49750 : checkPrefixCuts (2^48) 6524764161 10 Manual.Count131072.C049750.packed 64 cuts49750 = true := by
 decide +kernel
def cuts49751 : List PrefixCut := [⟨30,115697196,115697262⟩,
⟨64,249252364,249252502⟩]
theorem checked49751 : checkPrefixCuts (2^48) 6524895233 10 Manual.Count131072.C049751.packed 64 cuts49751 = true := by
 decide +kernel
def pointBounds49751 : List (Nat × Nat × Nat) := [(6524956672,111594824737737,111595211824421)]
theorem point_links_checked49751 : (cuts49751.take 1).map (fun c => (6524895233-1+2*2^10*c.k,111594709040541+c.lower,111595096127159+c.upper)) = pointBounds49751 := by
 decide +kernel
def cuts49752 : List PrefixCut := [⟨64,246227726,246227872⟩]
theorem checked49752 : checkPrefixCuts (2^48) 6525026305 10 Manual.Count131072.C049752.packed 64 cuts49752 = true := by
 decide +kernel
def cuts49753 : List PrefixCut := [⟨2,7419540,7419545⟩,
⟨64,249501179,249501319⟩]
theorem checked49753 : checkPrefixCuts (2^48) 6525157377 10 Manual.Count131072.C049753.packed 64 cuts49753 = true := by
 decide +kernel
def pointBounds49753 : List (Nat × Nat × Nat) := [(6525161472,111595211940171,111595599027078)]
theorem point_links_checked49753 : (cuts49753.take 1).map (fun c => (6525157377-1+2*2^10*c.k,111595204520631+c.lower,111595591607533+c.upper)) = pointBounds49753 := by
 decide +kernel
def cuts49754 : List PrefixCut := [⟨38,151018276,151018358⟩,
⟨64,252731357,252731495⟩]
theorem checked49754 : checkPrefixCuts (2^48) 6525288449 10 Manual.Count131072.C049754.packed 64 cuts49754 = true := by
 decide +kernel
def pointBounds49754 : List (Nat × Nat × Nat) := [(6525366272,111595605040086,111595992127210)]
theorem point_links_checked49754 : (cuts49754.take 1).map (fun c => (6525288449-1+2*2^10*c.k,111595454021810+c.lower,111595841108852+c.upper)) = pointBounds49754 := by
 decide +kernel
def cuts49755 : List PrefixCut := [⟨64,248369632,248369776⟩]
theorem checked49755 : checkPrefixCuts (2^48) 6525419521 10 Manual.Count131072.C049755.packed 64 cuts49755 = true := by
 decide +kernel
def cuts49756 : List PrefixCut := [⟨10,40589288,40589314⟩,
⟨64,256085618,256085761⟩]
theorem checked49756 : checkPrefixCuts (2^48) 6525550593 10 Manual.Count131072.C049756.packed 64 cuts49756 = true := by
 decide +kernel
def pointBounds49756 : List (Nat × Nat × Nat) := [(6525571072,111595995712087,111596382799437)]
theorem point_links_checked49756 : (cuts49756.take 1).map (fun c => (6525550593-1+2*2^10*c.k,111595955122799+c.lower,111596342210123+c.upper)) = pointBounds49756 := by
 decide +kernel
def cuts49757 : List PrefixCut := [⟨46,180123806,180123912⟩,
⟨64,249481130,249481276⟩]
theorem checked49757 : checkPrefixCuts (2^48) 6525681665 10 Manual.Count131072.C049757.packed 64 cuts49757 = true := by
 decide +kernel
def pointBounds49757 : List (Nat × Nat × Nat) := [(6525775872,111596391332223,111596778419796)]
theorem point_links_checked49757 : (cuts49757.take 1).map (fun c => (6525681665-1+2*2^10*c.k,111596211208417+c.lower,111596598295884+c.upper)) = pointBounds49757 := by
 decide +kernel
def cuts49758 : List PrefixCut := [⟨64,251546461,251546603⟩]
theorem checked49758 : checkPrefixCuts (2^48) 6525812737 10 Manual.Count131072.C049758.packed 64 cuts49758 = true := by
 decide +kernel
def cuts49759 : List PrefixCut := [⟨18,69916249,69916289⟩,
⟨64,251023830,251023971⟩]
theorem checked49759 : checkPrefixCuts (2^48) 6525943809 10 Manual.Count131072.C049759.packed 64 cuts49759 = true := by
 decide +kernel
def pointBounds49759 : List (Nat × Nat × Nat) := [(6525980672,111596782152257,111597169240052)]
theorem point_links_checked49759 : (cuts49759.take 1).map (fun c => (6525943809-1+2*2^10*c.k,111596712236008+c.lower,111597099323763+c.upper)) = pointBounds49759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000304
