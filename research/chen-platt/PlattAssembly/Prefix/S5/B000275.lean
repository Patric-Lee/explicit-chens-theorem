import PlattAssemblyKernel
import PlattCertificates.Count131072.C048800
import PlattCertificates.Count131072.C048801
import PlattCertificates.Count131072.C048802
import PlattCertificates.Count131072.C048803
import PlattCertificates.Count131072.C048804
import PlattCertificates.Count131072.C048805
import PlattCertificates.Count131072.C048806
import PlattCertificates.Count131072.C048807
import PlattCertificates.Count131072.C048808
import PlattCertificates.Count131072.C048809
import PlattCertificates.Count131072.C048810
import PlattCertificates.Count131072.C048811
import PlattCertificates.Count131072.C048812
import PlattCertificates.Count131072.C048813
import PlattCertificates.Count131072.C048814
import PlattCertificates.Count131072.C048815
import PlattCertificates.Count131072.C048816
import PlattCertificates.Count131072.C048817
import PlattCertificates.Count131072.C048818
import PlattCertificates.Count131072.C048819
import PlattCertificates.Count131072.C048820
import PlattCertificates.Count131072.C048821
import PlattCertificates.Count131072.C048822
import PlattCertificates.Count131072.C048823
import PlattCertificates.Count131072.C048824
import PlattCertificates.Count131072.C048825
import PlattCertificates.Count131072.C048826
import PlattCertificates.Count131072.C048827
import PlattCertificates.Count131072.C048828
import PlattCertificates.Count131072.C048829
import PlattCertificates.Count131072.C048830
import PlattCertificates.Count131072.C048831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000275
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48800 : List PrefixCut := [⟨40,157838778,157838870⟩,
⟨64,251204142,251204287⟩]
theorem checked48800 : checkPrefixCuts (2^48) 6400245761 10 Manual.Count131072.C048800.packed 64 cuts48800 = true := by
 decide +kernel
def pointBounds48800 : List (Nat × Nat × Nat) := [(6400327680,111354525908858,111354912858513)]
theorem point_links_checked48800 : (cuts48800.take 1).map (fun c => (6400245761-1+2*2^10*c.k,111354368070080+c.lower,111354755019643+c.upper)) = pointBounds48800 := by
 decide +kernel
def cuts48801 : List PrefixCut := [⟨64,255025008,255025155⟩]
theorem checked48801 : checkPrefixCuts (2^48) 6400376833 10 Manual.Count131072.C048801.packed 64 cuts48801 = true := by
 decide +kernel
def cuts48802 : List PrefixCut := [⟨10,40062949,40062973⟩,
⟨64,255767382,255767525⟩]
theorem checked48802 : checkPrefixCuts (2^48) 6400507905 10 Manual.Count131072.C048802.packed 64 cuts48802 = true := by
 decide +kernel
def pointBounds48802 : List (Nat × Nat × Nat) := [(6400528384,111354914362179,111355301312058)]
theorem point_links_checked48802 : (cuts48802.take 1).map (fun c => (6400507905-1+2*2^10*c.k,111354874299230+c.lower,111355261249085+c.upper)) = pointBounds48802 := by
 decide +kernel
def cuts48803 : List PrefixCut := [⟨44,175375303,175375402⟩,
⟨64,255586259,255586402⟩]
theorem checked48803 : checkPrefixCuts (2^48) 6400638977 10 Manual.Count131072.C048803.packed 64 cuts48803 = true := by
 decide +kernel
def pointBounds48803 : List (Nat × Nat × Nat) := [(6400729088,111355305441915,111355692392012)]
theorem point_links_checked48803 : (cuts48803.take 1).map (fun c => (6400638977-1+2*2^10*c.k,111355130066612+c.lower,111355517016610+c.upper)) = pointBounds48803 := by
 decide +kernel
def cuts48804 : List PrefixCut := [⟨64,254877427,254877574⟩]
theorem checked48804 : checkPrefixCuts (2^48) 6400770049 10 Manual.Count131072.C048804.packed 64 cuts48804 = true := by
 decide +kernel
def cuts48805 : List PrefixCut := [⟨14,58001923,58001952⟩,
⟨64,255311982,255312124⟩]
theorem checked48805 : checkPrefixCuts (2^48) 6400901121 10 Manual.Count131072.C048805.packed 64 cuts48805 = true := by
 decide +kernel
def pointBounds48805 : List (Nat × Nat × Nat) := [(6400929792,111355698532221,111356085482538)]
theorem point_links_checked48805 : (cuts48805.take 1).map (fun c => (6400901121-1+2*2^10*c.k,111355640530298+c.lower,111356027480586+c.upper)) = pointBounds48805 := by
 decide +kernel
def cuts48806 : List PrefixCut := [⟨48,192338006,192338119⟩,
⟨64,255482619,255482769⟩]
theorem checked48806 : checkPrefixCuts (2^48) 6401032193 10 Manual.Count131072.C048806.packed 64 cuts48806 = true := by
 decide +kernel
def pointBounds48806 : List (Nat × Nat × Nat) := [(6401130496,111356088180286,111356475130829)]
theorem point_links_checked48806 : (cuts48806.take 1).map (fun c => (6401032193-1+2*2^10*c.k,111355895842280+c.lower,111356282792710+c.upper)) = pointBounds48806 := by
 decide +kernel
def cuts48807 : List PrefixCut := [⟨64,253014943,253015087⟩]
theorem checked48807 : checkPrefixCuts (2^48) 6401163265 10 Manual.Count131072.C048807.packed 64 cuts48807 = true := by
 decide +kernel
def cuts48808 : List PrefixCut := [⟨18,68903234,68903276⟩,
⟨64,252789886,252790032⟩]
theorem checked48808 : checkPrefixCuts (2^48) 6401294337 10 Manual.Count131072.C048808.packed 64 cuts48808 = true := by
 decide +kernel
def pointBounds48808 : List (Nat × Nat × Nat) := [(6401331200,111356473243076,111356860193842)]
theorem point_links_checked48808 : (cuts48808.take 1).map (fun c => (6401294337-1+2*2^10*c.k,111356404339842+c.lower,111356791290566+c.upper)) = pointBounds48808 := by
 decide +kernel
def cuts48809 : List PrefixCut := [⟨52,208419193,208419311⟩,
⟨64,257005870,257006016⟩]
theorem checked48809 : checkPrefixCuts (2^48) 6401425409 10 Manual.Count131072.C048809.packed 64 cuts48809 = true := by
 decide +kernel
def pointBounds48809 : List (Nat × Nat × Nat) := [(6401531904,111356865548921,111357252499909)]
theorem point_links_checked48809 : (cuts48809.take 1).map (fun c => (6401425409-1+2*2^10*c.k,111356657129728+c.lower,111357044080598+c.upper)) = pointBounds48809 := by
 decide +kernel
def cuts48810 : List PrefixCut := [⟨64,255329774,255329927⟩]
theorem checked48810 : checkPrefixCuts (2^48) 6401556481 10 Manual.Count131072.C048810.packed 64 cuts48810 = true := by
 decide +kernel
def cuts48811 : List PrefixCut := [⟨22,88245184,88245235⟩,
⟨64,255720256,255720403⟩]
theorem checked48811 : checkPrefixCuts (2^48) 6401687553 10 Manual.Count131072.C048811.packed 64 cuts48811 = true := by
 decide +kernel
def pointBounds48811 : List (Nat × Nat × Nat) := [(6401732608,111357257710556,111357644661776)]
theorem point_links_checked48811 : (cuts48811.take 1).map (fun c => (6401687553-1+2*2^10*c.k,111357169465372+c.lower,111357556416541+c.upper)) = pointBounds48811 := by
 decide +kernel
def cuts48812 : List PrefixCut := [⟨56,222124154,222124284⟩,
⟨64,252637331,252637479⟩]
theorem checked48812 : checkPrefixCuts (2^48) 6401818625 10 Manual.Count131072.C048812.packed 64 cuts48812 = true := by
 decide +kernel
def pointBounds48812 : List (Nat × Nat × Nat) := [(6401933312,111357647309782,111358034261228)]
theorem point_links_checked48812 : (cuts48812.take 1).map (fun c => (6401818625-1+2*2^10*c.k,111357425185628+c.lower,111357812136944+c.upper)) = pointBounds48812 := by
 decide +kernel
def cuts48813 : List PrefixCut := [⟨64,256237401,256237552⟩]
theorem checked48813 : checkPrefixCuts (2^48) 6401949697 10 Manual.Count131072.C048813.packed 64 cuts48813 = true := by
 decide +kernel
def cuts48814 : List PrefixCut := [⟨26,105914033,105914093⟩,
⟨64,259001993,259002140⟩]
theorem checked48814 : checkPrefixCuts (2^48) 6402080769 10 Manual.Count131072.C048814.packed 64 cuts48814 = true := by
 decide +kernel
def pointBounds48814 : List (Nat × Nat × Nat) := [(6402134016,111358039974393,111358426926068)]
theorem point_links_checked48814 : (cuts48814.take 1).map (fun c => (6402080769-1+2*2^10*c.k,111357934060360+c.lower,111358321011975+c.upper)) = pointBounds48814 := by
 decide +kernel
def cuts48815 : List PrefixCut := [⟨60,239608383,239608520⟩,
⟨64,255831241,255831388⟩]
theorem checked48815 : checkPrefixCuts (2^48) 6402211841 10 Manual.Count131072.C048815.packed 64 cuts48815 = true := by
 decide +kernel
def pointBounds48815 : List (Nat × Nat × Nat) := [(6402334720,111358432670736,111358819622635)]
theorem point_links_checked48815 : (cuts48815.take 1).map (fun c => (6402211841-1+2*2^10*c.k,111358193062353+c.lower,111358580014115+c.upper)) = pointBounds48815 := by
 decide +kernel
def cuts48816 : List PrefixCut := [⟨64,255474246,255474391⟩]
theorem checked48816 : checkPrefixCuts (2^48) 6402342913 10 Manual.Count131072.C048816.packed 64 cuts48816 = true := by
 decide +kernel
def cuts48817 : List PrefixCut := [⟨30,119931734,119931805⟩,
⟨64,255820738,255820886⟩]
theorem checked48817 : checkPrefixCuts (2^48) 6402473985 10 Manual.Count131072.C048817.packed 64 cuts48817 = true := by
 decide +kernel
def pointBounds48817 : List (Nat × Nat × Nat) := [(6402535424,111358824299574,111359211251699)]
theorem point_links_checked48817 : (cuts48817.take 1).map (fun c => (6402473985-1+2*2^10*c.k,111358704367840+c.lower,111359091319894+c.upper)) = pointBounds48817 := by
 decide +kernel
def cuts48818 : List PrefixCut := [⟨64,254364776,254364929⟩]
theorem checked48818 : checkPrefixCuts (2^48) 6402605057 10 Manual.Count131072.C048818.packed 64 cuts48818 = true := by
 decide +kernel
def pointBounds48818 : List (Nat × Nat × Nat) := [(6402736128,111359214553354,111359601505709)]
theorem point_links_checked48818 : (cuts48818.take 1).map (fun c => (6402605057-1+2*2^10*c.k,111358960188578+c.lower,111359347140780+c.upper)) = pointBounds48818 := by
 decide +kernel
def cuts48819 : List PrefixCut := [⟨64,254667272,254667416⟩]
theorem checked48819 : checkPrefixCuts (2^48) 6402736129 10 Manual.Count131072.C048819.packed 64 cuts48819 = true := by
 decide +kernel
def cuts48820 : List PrefixCut := [⟨34,137376619,137376697⟩,
⟨64,256200697,256200839⟩]
theorem checked48820 : checkPrefixCuts (2^48) 6402867201 10 Manual.Count131072.C048820.packed 64 cuts48820 = true := by
 decide +kernel
def pointBounds48820 : List (Nat × Nat × Nat) := [(6402936832,111359606597245,111359993549822)]
theorem point_links_checked48820 : (cuts48820.take 1).map (fun c => (6402867201-1+2*2^10*c.k,111359469220626+c.lower,111359856173125+c.upper)) = pointBounds48820 := by
 decide +kernel
def cuts48821 : List PrefixCut := [⟨64,256459196,256459351⟩]
theorem checked48821 : checkPrefixCuts (2^48) 6402998273 10 Manual.Count131072.C048821.packed 64 cuts48821 = true := by
 decide +kernel
def cuts48822 : List PrefixCut := [⟨4,16484599,16484609⟩,
⟨64,252453719,252453865⟩]
theorem checked48822 : checkPrefixCuts (2^48) 6403129345 10 Manual.Count131072.C048822.packed 64 cuts48822 = true := by
 decide +kernel
def pointBounds48822 : List (Nat × Nat × Nat) := [(6403137536,111359998365118,111360385317924)]
theorem point_links_checked48822 : (cuts48822.take 1).map (fun c => (6403129345-1+2*2^10*c.k,111359981880519+c.lower,111360368833315+c.upper)) = pointBounds48822 := by
 decide +kernel
def cuts48823 : List PrefixCut := [⟨38,152665418,152665504⟩,
⟨64,257152017,257152162⟩]
theorem checked48823 : checkPrefixCuts (2^48) 6403260417 10 Manual.Count131072.C048823.packed 64 cuts48823 = true := by
 decide +kernel
def pointBounds48823 : List (Nat × Nat × Nat) := [(6403338240,111360386999656,111360773952684)]
theorem point_links_checked48823 : (cuts48823.take 1).map (fun c => (6403260417-1+2*2^10*c.k,111360234334238+c.lower,111360621287180+c.upper)) = pointBounds48823 := by
 decide +kernel
def cuts48824 : List PrefixCut := [⟨64,253630204,253630346⟩]
theorem checked48824 : checkPrefixCuts (2^48) 6403391489 10 Manual.Count131072.C048824.packed 64 cuts48824 = true := by
 decide +kernel
def cuts48825 : List PrefixCut := [⟨8,31077035,31077053⟩,
⟨64,256130488,256130640⟩]
theorem checked48825 : checkPrefixCuts (2^48) 6403522561 10 Manual.Count131072.C048825.packed 64 cuts48825 = true := by
 decide +kernel
def pointBounds48825 : List (Nat × Nat × Nat) := [(6403538944,111360776193494,111361163146741)]
theorem point_links_checked48825 : (cuts48825.take 1).map (fun c => (6403522561-1+2*2^10*c.k,111360745116459+c.lower,111361132069688+c.upper)) = pointBounds48825 := by
 decide +kernel
def cuts48826 : List PrefixCut := [⟨42,167732513,167732612⟩,
⟨64,255465926,255466075⟩]
theorem checked48826 : checkPrefixCuts (2^48) 6403653633 10 Manual.Count131072.C048826.packed 64 cuts48826 = true := by
 decide +kernel
def pointBounds48826 : List (Nat × Nat × Nat) := [(6403739648,111361168979460,111361555932940)]
theorem point_links_checked48826 : (cuts48826.take 1).map (fun c => (6403653633-1+2*2^10*c.k,111361001246947+c.lower,111361388200328+c.upper)) = pointBounds48826 := by
 decide +kernel
def cuts48827 : List PrefixCut := [⟨64,257614468,257614621⟩]
theorem checked48827 : checkPrefixCuts (2^48) 6403784705 10 Manual.Count131072.C048827.packed 64 cuts48827 = true := by
 decide +kernel
def cuts48828 : List PrefixCut := [⟨12,47074173,47074200⟩,
⟨64,255411520,255411665⟩]
theorem checked48828 : checkPrefixCuts (2^48) 6403915777 10 Manual.Count131072.C048828.packed 64 cuts48828 = true := by
 decide +kernel
def pointBounds48828 : List (Nat × Nat × Nat) := [(6403940352,111361561401514,111361948355224)]
theorem point_links_checked48828 : (cuts48828.take 1).map (fun c => (6403915777-1+2*2^10*c.k,111361514327341+c.lower,111361901281024+c.upper)) = pointBounds48828 := by
 decide +kernel
def cuts48829 : List PrefixCut := [⟨46,182929625,182929730⟩,
⟨64,254307490,254307636⟩]
theorem checked48829 : checkPrefixCuts (2^48) 6404046849 10 Manual.Count131072.C048829.packed 64 cuts48829 = true := by
 decide +kernel
def pointBounds48829 : List (Nat × Nat × Nat) := [(6404141056,111361952668486,111362339622419)]
theorem point_links_checked48829 : (cuts48829.take 1).map (fun c => (6404046849-1+2*2^10*c.k,111361769738861+c.lower,111362156692689+c.upper)) = pointBounds48829 := by
 decide +kernel
def cuts48830 : List PrefixCut := [⟨64,254038565,254038712⟩]
theorem checked48830 : checkPrefixCuts (2^48) 6404177921 10 Manual.Count131072.C048830.packed 64 cuts48830 = true := by
 decide +kernel
def cuts48831 : List PrefixCut := [⟨16,63772537,63772573⟩,
⟨64,261373069,261373220⟩]
theorem checked48831 : checkPrefixCuts (2^48) 6404308993 10 Manual.Count131072.C048831.packed 64 cuts48831 = true := by
 decide +kernel
def pointBounds48831 : List (Nat × Nat × Nat) := [(6404341760,111362341857453,111362728811610)]
theorem point_links_checked48831 : (cuts48831.take 1).map (fun c => (6404308993-1+2*2^10*c.k,111362278084916+c.lower,111362665039037+c.upper)) = pointBounds48831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000275
