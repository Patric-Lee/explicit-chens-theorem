import PlattAssemblyKernel
import PlattCertificates.Count131072.C068768
import PlattCertificates.Count131072.C068769
import PlattCertificates.Count131072.C068770
import PlattCertificates.Count131072.C068771
import PlattCertificates.Count131072.C068772
import PlattCertificates.Count131072.C068773
import PlattCertificates.Count131072.C068774
import PlattCertificates.Count131072.C068775
import PlattCertificates.Count131072.C068776
import PlattCertificates.Count131072.C068777
import PlattCertificates.Count131072.C068778
import PlattCertificates.Count131072.C068779
import PlattCertificates.Count131072.C068780
import PlattCertificates.Count131072.C068781
import PlattCertificates.Count131072.C068782
import PlattCertificates.Count131072.C068783
import PlattCertificates.Count131072.C068784
import PlattCertificates.Count131072.C068785
import PlattCertificates.Count131072.C068786
import PlattCertificates.Count131072.C068787
import PlattCertificates.Count131072.C068788
import PlattCertificates.Count131072.C068789
import PlattCertificates.Count131072.C068790
import PlattCertificates.Count131072.C068791
import PlattCertificates.Count131072.C068792
import PlattCertificates.Count131072.C068793
import PlattCertificates.Count131072.C068794
import PlattCertificates.Count131072.C068795
import PlattCertificates.Count131072.C068796
import PlattCertificates.Count131072.C068797
import PlattCertificates.Count131072.C068798
import PlattCertificates.Count131072.C068799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000274
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68768 : List PrefixCut := [⟨64,177015143,177015241⟩]
theorem checked68768 : checkPrefixCuts (2^48) 9017491457 10 Manual.Count131072.C068768.packed 64 cuts68768 = true := by
 decide +kernel
def cuts68769 : List PrefixCut := [⟨59,163465940,163466039⟩,
⟨64,177106210,177106317⟩]
theorem checked68769 : checkPrefixCuts (2^48) 9017622529 10 Manual.Count131072.C068769.packed 64 cuts68769 = true := by
 decide +kernel
def pointBounds68769 : List (Nat × Nat × Nat) := [(9017743360,115596231426102,115596620803478)]
theorem point_links_checked68769 : (cuts68769.take 1).map (fun c => (9017622529-1+2*2^10*c.k,115596067960162+c.lower,115596457337439+c.upper)) = pointBounds68769 := by
 decide +kernel
def cuts68770 : List PrefixCut := [⟨64,177478189,177478301⟩]
theorem checked68770 : checkPrefixCuts (2^48) 9017753601 10 Manual.Count131072.C068770.packed 64 cuts68770 = true := by
 decide +kernel
def cuts68771 : List PrefixCut := [⟨64,178568062,178568164⟩]
theorem checked68771 : checkPrefixCuts (2^48) 9017884673 10 Manual.Count131072.C068771.packed 64 cuts68771 = true := by
 decide +kernel
def cuts68772 : List PrefixCut := [⟨5,13951983,13951993⟩,
⟨64,180469419,180469525⟩]
theorem checked68772 : checkPrefixCuts (2^48) 9018015745 10 Manual.Count131072.C068772.packed 64 cuts68772 = true := by
 decide +kernel
def pointBounds68772 : List (Nat × Nat × Nat) := [(9018025984,115596615064606,115597004442214)]
theorem point_links_checked68772 : (cuts68772.take 1).map (fun c => (9018015745-1+2*2^10*c.k,115596601112623+c.lower,115596990490221+c.upper)) = pointBounds68772 := by
 decide +kernel
def cuts68773 : List PrefixCut := [⟨64,181496776,181496882⟩]
theorem checked68773 : checkPrefixCuts (2^48) 9018146817 10 Manual.Count131072.C068773.packed 64 cuts68773 = true := by
 decide +kernel
def cuts68774 : List PrefixCut := [⟨15,43040726,43040753⟩,
⟨64,180776285,180776390⟩]
theorem checked68774 : checkPrefixCuts (2^48) 9018277889 10 Manual.Count131072.C068774.packed 64 cuts68774 = true := by
 decide +kernel
def pointBounds68774 : List (Nat × Nat × Nat) := [(9018308608,115597006119544,115597395497381)]
theorem point_links_checked68774 : (cuts68774.take 1).map (fun c => (9018277889-1+2*2^10*c.k,115596963078818+c.lower,115597352456628+c.upper)) = pointBounds68774 := by
 decide +kernel
def cuts68775 : List PrefixCut := [⟨64,180742443,180742548⟩]
theorem checked68775 : checkPrefixCuts (2^48) 9018408961 10 Manual.Count131072.C068775.packed 64 cuts68775 = true := by
 decide +kernel
def cuts68776 : List PrefixCut := [⟨25,68913019,68913063⟩,
⟨64,176432776,176432884⟩]
theorem checked68776 : checkPrefixCuts (2^48) 9018540033 10 Manual.Count131072.C068776.packed 64 cuts68776 = true := by
 decide +kernel
def pointBounds68776 : List (Nat × Nat × Nat) := [(9018591232,115597393510565,115597782888629)]
theorem point_links_checked68776 : (cuts68776.take 1).map (fun c => (9018540033-1+2*2^10*c.k,115597324597546+c.lower,115597713975566+c.upper)) = pointBounds68776 := by
 decide +kernel
def cuts68777 : List PrefixCut := [⟨64,178365228,178365334⟩]
theorem checked68777 : checkPrefixCuts (2^48) 9018671105 10 Manual.Count131072.C068777.packed 64 cuts68777 = true := by
 decide +kernel
def cuts68778 : List PrefixCut := [⟨35,98310439,98310500⟩,
⟨64,178737157,178737263⟩]
theorem checked68778 : checkPrefixCuts (2^48) 9018802177 10 Manual.Count131072.C068778.packed 64 cuts68778 = true := by
 decide +kernel
def pointBounds68778 : List (Nat × Nat × Nat) := [(9018873856,115597777705989,115598167084284)]
theorem point_links_checked68778 : (cuts68778.take 1).map (fun c => (9018802177-1+2*2^10*c.k,115597679395550+c.lower,115598068773784+c.upper)) = pointBounds68778 := by
 decide +kernel
def cuts68779 : List PrefixCut := [⟨64,176674741,176674847⟩]
theorem checked68779 : checkPrefixCuts (2^48) 9018933249 10 Manual.Count131072.C068779.packed 64 cuts68779 = true := by
 decide +kernel
def cuts68780 : List PrefixCut := [⟨45,127955753,127955829⟩,
⟨64,179824269,179824376⟩]
theorem checked68780 : checkPrefixCuts (2^48) 9019064321 10 Manual.Count131072.C068780.packed 64 cuts68780 = true := by
 decide +kernel
def pointBounds68780 : List (Nat × Nat × Nat) := [(9019156480,115598162763201,115598552141723)]
theorem point_links_checked68780 : (cuts68780.take 1).map (fun c => (9019064321-1+2*2^10*c.k,115598034807448+c.lower,115598424185894+c.upper)) = pointBounds68780 := by
 decide +kernel
def cuts68781 : List PrefixCut := [⟨64,178292451,178292551⟩]
theorem checked68781 : checkPrefixCuts (2^48) 9019195393 10 Manual.Count131072.C068781.packed 64 cuts68781 = true := by
 decide +kernel
def cuts68782 : List PrefixCut := [⟨55,155009023,155009119⟩,
⟨64,180786462,180786569⟩]
theorem checked68782 : checkPrefixCuts (2^48) 9019326465 10 Manual.Count131072.C068782.packed 64 cuts68782 = true := by
 decide +kernel
def pointBounds68782 : List (Nat × Nat × Nat) := [(9019439104,115598547933191,115598937311940)]
theorem point_links_checked68782 : (cuts68782.take 1).map (fun c => (9019326465-1+2*2^10*c.k,115598392924168+c.lower,115598782302821+c.upper)) = pointBounds68782 := by
 decide +kernel
def cuts68783 : List PrefixCut := [⟨64,177725530,177725634⟩]
theorem checked68783 : checkPrefixCuts (2^48) 9019457537 10 Manual.Count131072.C068783.packed 64 cuts68783 = true := by
 decide +kernel
def cuts68784 : List PrefixCut := [⟨64,177691741,177691847⟩]
theorem checked68784 : checkPrefixCuts (2^48) 9019588609 10 Manual.Count131072.C068784.packed 64 cuts68784 = true := by
 decide +kernel
def cuts68785 : List PrefixCut := [⟨1,3276694,3276696⟩,
⟨64,181184279,181184390⟩]
theorem checked68785 : checkPrefixCuts (2^48) 9019719681 10 Manual.Count131072.C068785.packed 64 cuts68785 = true := by
 decide +kernel
def pointBounds68785 : List (Nat × Nat × Nat) := [(9019721728,115598932404595,115599321783567)]
theorem point_links_checked68785 : (cuts68785.take 1).map (fun c => (9019719681-1+2*2^10*c.k,115598929127901+c.lower,115599318506871+c.upper)) = pointBounds68785 := by
 decide +kernel
def cuts68786 : List PrefixCut := [⟨64,181618528,181618633⟩]
theorem checked68786 : checkPrefixCuts (2^48) 9019850753 10 Manual.Count131072.C068786.packed 64 cuts68786 = true := by
 decide +kernel
def cuts68787 : List PrefixCut := [⟨11,29988646,29988663⟩,
⟨64,176061305,176061407⟩]
theorem checked68787 : checkPrefixCuts (2^48) 9019981825 10 Manual.Count131072.C068787.packed 64 cuts68787 = true := by
 decide +kernel
def pointBounds68787 : List (Nat × Nat × Nat) := [(9020004352,115599321919354,115599711298557)]
theorem point_links_checked68787 : (cuts68787.take 1).map (fun c => (9019981825-1+2*2^10*c.k,115599291930708+c.lower,115599681309894+c.upper)) = pointBounds68787 := by
 decide +kernel
def cuts68788 : List PrefixCut := [⟨64,178367918,178368030⟩]
theorem checked68788 : checkPrefixCuts (2^48) 9020112897 10 Manual.Count131072.C068788.packed 64 cuts68788 = true := by
 decide +kernel
def cuts68789 : List PrefixCut := [⟨21,59101749,59101779⟩,
⟨64,179457496,179457597⟩]
theorem checked68789 : checkPrefixCuts (2^48) 9020243969 10 Manual.Count131072.C068789.packed 64 cuts68789 = true := by
 decide +kernel
def pointBounds68789 : List (Nat × Nat × Nat) := [(9020286976,115599705461680,115600094841110)]
theorem point_links_checked68789 : (cuts68789.take 1).map (fun c => (9020243969-1+2*2^10*c.k,115599646359931+c.lower,115600035739331+c.upper)) = pointBounds68789 := by
 decide +kernel
def cuts68790 : List PrefixCut := [⟨64,179891746,179891852⟩]
theorem checked68790 : checkPrefixCuts (2^48) 9020375041 10 Manual.Count131072.C068790.packed 64 cuts68790 = true := by
 decide +kernel
def cuts68791 : List PrefixCut := [⟨31,86060032,86060083⟩,
⟨64,178640985,178641082⟩]
theorem checked68791 : checkPrefixCuts (2^48) 9020506113 10 Manual.Count131072.C068791.packed 64 cuts68791 = true := by
 decide +kernel
def pointBounds68791 : List (Nat × Nat × Nat) := [(9020569600,115600091769205,115600481148863)]
theorem point_links_checked68791 : (cuts68791.take 1).map (fun c => (9020506113-1+2*2^10*c.k,115600005709173+c.lower,115600395088780+c.upper)) = pointBounds68791 := by
 decide +kernel
def cuts68792 : List PrefixCut := [⟨64,180853831,180853931⟩]
theorem checked68792 : checkPrefixCuts (2^48) 9020637185 10 Manual.Count131072.C068792.packed 64 cuts68792 = true := by
 decide +kernel
def cuts68793 : List PrefixCut := [⟨41,113734344,113734417⟩,
⟨64,177418876,177418985⟩]
theorem checked68793 : checkPrefixCuts (2^48) 9020768257 10 Manual.Count131072.C068793.packed 64 cuts68793 = true := by
 decide +kernel
def pointBounds68793 : List (Nat × Nat × Nat) := [(9020852224,115600478938333,115600868318210)]
theorem point_links_checked68793 : (cuts68793.take 1).map (fun c => (9020768257-1+2*2^10*c.k,115600365203989+c.lower,115600754583793+c.upper)) = pointBounds68793 := by
 decide +kernel
def cuts68794 : List PrefixCut := [⟨64,178071553,178071656⟩]
theorem checked68794 : checkPrefixCuts (2^48) 9020899329 10 Manual.Count131072.C068794.packed 64 cuts68794 = true := by
 decide +kernel
def cuts68795 : List PrefixCut := [⟨51,145432048,145432135⟩,
⟨64,181501180,181501287⟩]
theorem checked68795 : checkPrefixCuts (2^48) 9021030401 10 Manual.Count131072.C068795.packed 64 cuts68795 = true := by
 decide +kernel
def pointBounds68795 : List (Nat × Nat × Nat) := [(9021134848,115600866126466,115601255506569)]
theorem point_links_checked68795 : (cuts68795.take 1).map (fun c => (9021030401-1+2*2^10*c.k,115600720694418+c.lower,115601110074434+c.upper)) = pointBounds68795 := by
 decide +kernel
def cuts68796 : List PrefixCut := [⟨64,176163086,176163190⟩]
theorem checked68796 : checkPrefixCuts (2^48) 9021161473 10 Manual.Count131072.C068796.packed 64 cuts68796 = true := by
 decide +kernel
def cuts68797 : List PrefixCut := [⟨61,171324436,171324537⟩,
⟨64,179467826,179467932⟩]
theorem checked68797 : checkPrefixCuts (2^48) 9021292545 10 Manual.Count131072.C068797.packed 64 cuts68797 = true := by
 decide +kernel
def pointBounds68797 : List (Nat × Nat × Nat) := [(9021417472,115601249683120,115601639063448)]
theorem point_links_checked68797 : (cuts68797.take 1).map (fun c => (9021292545-1+2*2^10*c.k,115601078358684+c.lower,115601467738911+c.upper)) = pointBounds68797 := by
 decide +kernel
def cuts68798 : List PrefixCut := [⟨64,181867671,181867775⟩]
theorem checked68798 : checkPrefixCuts (2^48) 9021423617 10 Manual.Count131072.C068798.packed 64 cuts68798 = true := by
 decide +kernel
def cuts68799 : List PrefixCut := [⟨64,174876212,174876310⟩]
theorem checked68799 : checkPrefixCuts (2^48) 9021554689 10 Manual.Count131072.C068799.packed 64 cuts68799 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000274
