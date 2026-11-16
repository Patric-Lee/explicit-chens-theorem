import PlattAssemblyKernel
import PlattCertificates.Count131072.C061824
import PlattCertificates.Count131072.C061825
import PlattCertificates.Count131072.C061826
import PlattCertificates.Count131072.C061827
import PlattCertificates.Count131072.C061828
import PlattCertificates.Count131072.C061829
import PlattCertificates.Count131072.C061830
import PlattCertificates.Count131072.C061831
import PlattCertificates.Count131072.C061832
import PlattCertificates.Count131072.C061833
import PlattCertificates.Count131072.C061834
import PlattCertificates.Count131072.C061835
import PlattCertificates.Count131072.C061836
import PlattCertificates.Count131072.C061837
import PlattCertificates.Count131072.C061838
import PlattCertificates.Count131072.C061839
import PlattCertificates.Count131072.C061840
import PlattCertificates.Count131072.C061841
import PlattCertificates.Count131072.C061842
import PlattCertificates.Count131072.C061843
import PlattCertificates.Count131072.C061844
import PlattCertificates.Count131072.C061845
import PlattCertificates.Count131072.C061846
import PlattCertificates.Count131072.C061847
import PlattCertificates.Count131072.C061848
import PlattCertificates.Count131072.C061849
import PlattCertificates.Count131072.C061850
import PlattCertificates.Count131072.C061851
import PlattCertificates.Count131072.C061852
import PlattCertificates.Count131072.C061853
import PlattCertificates.Count131072.C061854
import PlattCertificates.Count131072.C061855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61824 : List PrefixCut := [⟨64,198831711,198831826⟩]
theorem checked61824 : checkPrefixCuts (2^48) 8107327489 10 Manual.Count131072.C061824.packed 64 cuts61824 = true := by
 decide +kernel
def cuts61825 : List PrefixCut := [⟨20,62700580,62700618⟩,
⟨64,202126670,202126787⟩]
theorem checked61825 : checkPrefixCuts (2^48) 8107458561 10 Manual.Count131072.C061825.packed 64 cuts61825 = true := by
 decide +kernel
def pointBounds61825 : List (Nat × Nat × Nat) := [(8107499520,114286612842192,114287001461038)]
theorem point_links_checked61825 : (cuts61825.take 1).map (fun c => (8107458561-1+2*2^10*c.k,114286550141612+c.lower,114286938760420+c.upper)) = pointBounds61825 := by
 decide +kernel
def cuts61826 : List PrefixCut := [⟨64,195561846,195561959⟩]
theorem checked61826 : checkPrefixCuts (2^48) 8107589633 10 Manual.Count131072.C061826.packed 64 cuts61826 = true := by
 decide +kernel
def cuts61827 : List PrefixCut := [⟨16,49818646,49818673⟩,
⟨64,199273392,199273504⟩]
theorem checked61827 : checkPrefixCuts (2^48) 8107720705 10 Manual.Count131072.C061827.packed 64 cuts61827 = true := by
 decide +kernel
def pointBounds61827 : List (Nat × Nat × Nat) := [(8107753472,114286997648774,114287386267839)]
theorem point_links_checked61827 : (cuts61827.take 1).map (fun c => (8107720705-1+2*2^10*c.k,114286947830128+c.lower,114287336449166+c.upper)) = pointBounds61827 := by
 decide +kernel
def cuts61828 : List PrefixCut := [⟨64,199547890,199548000⟩]
theorem checked61828 : checkPrefixCuts (2^48) 8107851777 10 Manual.Count131072.C061828.packed 64 cuts61828 = true := by
 decide +kernel
def cuts61829 : List PrefixCut := [⟨12,36590370,36590390⟩,
⟨64,199544656,199544768⟩]
theorem checked61829 : checkPrefixCuts (2^48) 8107982849 10 Manual.Count131072.C061829.packed 64 cuts61829 = true := by
 decide +kernel
def pointBounds61829 : List (Nat × Nat × Nat) := [(8108007424,114287383241780,114287771861060)]
theorem point_links_checked61829 : (cuts61829.take 1).map (fun c => (8107982849-1+2*2^10*c.k,114287346651410+c.lower,114287735270670+c.upper)) = pointBounds61829 := by
 decide +kernel
def cuts61830 : List PrefixCut := [⟨64,200756445,200756561⟩]
theorem checked61830 : checkPrefixCuts (2^48) 8108113921 10 Manual.Count131072.C061830.packed 64 cuts61830 = true := by
 decide +kernel
def cuts61831 : List PrefixCut := [⟨8,24925094,24925108⟩,
⟨64,200267198,200267312⟩]
theorem checked61831 : checkPrefixCuts (2^48) 8108244993 10 Manual.Count131072.C061831.packed 64 cuts61831 = true := by
 decide +kernel
def pointBounds61831 : List (Nat × Nat × Nat) := [(8108261376,114287771877605,114288160497107)]
theorem point_links_checked61831 : (cuts61831.take 1).map (fun c => (8108244993-1+2*2^10*c.k,114287746952511+c.lower,114288135571999+c.upper)) = pointBounds61831 := by
 decide +kernel
def cuts61832 : List PrefixCut := [⟨64,201027675,201027787⟩]
theorem checked61832 : checkPrefixCuts (2^48) 8108376065 10 Manual.Count131072.C061832.packed 64 cuts61832 = true := by
 decide +kernel
def cuts61833 : List PrefixCut := [⟨4,13121707,13121714⟩,
⟨64,199740026,199740137⟩]
theorem checked61833 : checkPrefixCuts (2^48) 8108507137 10 Manual.Count131072.C061833.packed 64 cuts61833 = true := by
 decide +kernel
def pointBounds61833 : List (Nat × Nat × Nat) := [(8108515328,114288161369091,114288549988812)]
theorem point_links_checked61833 : (cuts61833.take 1).map (fun c => (8108507137-1+2*2^10*c.k,114288148247384+c.lower,114288536867098+c.upper)) = pointBounds61833 := by
 decide +kernel
def cuts61834 : List PrefixCut := [⟨64,197792872,197792989⟩]
theorem checked61834 : checkPrefixCuts (2^48) 8108638209 10 Manual.Count131072.C061834.packed 64 cuts61834 = true := by
 decide +kernel
def pointBounds61834 : List (Nat × Nat × Nat) := [(8108769280,114288545780282,114288934400224)]
theorem point_links_checked61834 : (cuts61834.take 1).map (fun c => (8108638209-1+2*2^10*c.k,114288347987410+c.lower,114288736607235+c.upper)) = pointBounds61834 := by
 decide +kernel
def cuts61835 : List PrefixCut := [⟨64,198518669,198518771⟩]
theorem checked61835 : checkPrefixCuts (2^48) 8108769281 10 Manual.Count131072.C061835.packed 64 cuts61835 = true := by
 decide +kernel
def cuts61836 : List PrefixCut := [⟨60,186574756,186574866⟩,
⟨64,198307176,198307293⟩]
theorem checked61836 : checkPrefixCuts (2^48) 8108900353 10 Manual.Count131072.C061836.packed 64 cuts61836 = true := by
 decide +kernel
def pointBounds61836 : List (Nat × Nat × Nat) := [(8109023232,114288930873707,114289319493861)]
theorem point_links_checked61836 : (cuts61836.take 1).map (fun c => (8108900353-1+2*2^10*c.k,114288744298951+c.lower,114289132918995+c.upper)) = pointBounds61836 := by
 decide +kernel
def cuts61837 : List PrefixCut := [⟨64,201636241,201636353⟩]
theorem checked61837 : checkPrefixCuts (2^48) 8109031425 10 Manual.Count131072.C061837.packed 64 cuts61837 = true := by
 decide +kernel
def cuts61838 : List PrefixCut := [⟨56,175357341,175357435⟩,
⟨64,200175133,200175241⟩]
theorem checked61838 : checkPrefixCuts (2^48) 8109162497 10 Manual.Count131072.C061838.packed 64 cuts61838 = true := by
 decide +kernel
def pointBounds61838 : List (Nat × Nat × Nat) := [(8109277184,114289319599709,114289708220076)]
theorem point_links_checked61838 : (cuts61838.take 1).map (fun c => (8109162497-1+2*2^10*c.k,114289144242368+c.lower,114289532862641+c.upper)) = pointBounds61838 := by
 decide +kernel
def cuts61839 : List PrefixCut := [⟨64,197499224,197499334⟩]
theorem checked61839 : checkPrefixCuts (2^48) 8109293569 10 Manual.Count131072.C061839.packed 64 cuts61839 = true := by
 decide +kernel
def cuts61840 : List PrefixCut := [⟨52,160530853,160530947⟩,
⟨64,196767145,196767260⟩]
theorem checked61840 : checkPrefixCuts (2^48) 8109424641 10 Manual.Count131072.C061840.packed 64 cuts61840 = true := by
 decide +kernel
def pointBounds61840 : List (Nat × Nat × Nat) := [(8109531136,114289702447578,114290091068163)]
theorem point_links_checked61840 : (cuts61840.take 1).map (fun c => (8109424641-1+2*2^10*c.k,114289541916725+c.lower,114289930537216+c.upper)) = pointBounds61840 := by
 decide +kernel
def cuts61841 : List PrefixCut := [⟨64,197076343,197076462⟩]
theorem checked61841 : checkPrefixCuts (2^48) 8109555713 10 Manual.Count131072.C061841.packed 64 cuts61841 = true := by
 decide +kernel
def cuts61842 : List PrefixCut := [⟨48,151050404,151050487⟩,
⟨64,201168741,201168852⟩]
theorem checked61842 : checkPrefixCuts (2^48) 8109686785 10 Manual.Count131072.C061842.packed 64 cuts61842 = true := by
 decide +kernel
def pointBounds61842 : List (Nat × Nat × Nat) := [(8109785088,114290086810617,114290475431425)]
theorem point_links_checked61842 : (cuts61842.take 1).map (fun c => (8109686785-1+2*2^10*c.k,114289935760213+c.lower,114290324380938+c.upper)) = pointBounds61842 := by
 decide +kernel
def cuts61843 : List PrefixCut := [⟨64,198597093,198597205⟩]
theorem checked61843 : checkPrefixCuts (2^48) 8109817857 10 Manual.Count131072.C061843.packed 64 cuts61843 = true := by
 decide +kernel
def cuts61844 : List PrefixCut := [⟨44,137197425,137197501⟩,
⟨64,201266332,201266446⟩]
theorem checked61844 : checkPrefixCuts (2^48) 8109948929 10 Manual.Count131072.C061844.packed 64 cuts61844 = true := by
 decide +kernel
def pointBounds61844 : List (Nat × Nat × Nat) := [(8110039040,114290472723472,114290861344496)]
theorem point_links_checked61844 : (cuts61844.take 1).map (fun c => (8109948929-1+2*2^10*c.k,114290335526047+c.lower,114290724146995+c.upper)) = pointBounds61844 := by
 decide +kernel
def cuts61845 : List PrefixCut := [⟨64,202234863,202234981⟩]
theorem checked61845 : checkPrefixCuts (2^48) 8110080001 10 Manual.Count131072.C061845.packed 64 cuts61845 = true := by
 decide +kernel
def cuts61846 : List PrefixCut := [⟨40,123727105,123727179⟩,
⟨64,199212174,199212289⟩]
theorem checked61846 : checkPrefixCuts (2^48) 8110211073 10 Manual.Count131072.C061846.packed 64 cuts61846 = true := by
 decide +kernel
def pointBounds61846 : List (Nat × Nat × Nat) := [(8110292992,114290862754347,114291251375601)]
theorem point_links_checked61846 : (cuts61846.take 1).map (fun c => (8110211073-1+2*2^10*c.k,114290739027242+c.lower,114291127648422+c.upper)) = pointBounds61846 := by
 decide +kernel
def cuts61847 : List PrefixCut := [⟨64,199660123,199660237⟩]
theorem checked61847 : checkPrefixCuts (2^48) 8110342145 10 Manual.Count131072.C061847.packed 64 cuts61847 = true := by
 decide +kernel
def cuts61848 : List PrefixCut := [⟨36,112964630,112964693⟩,
⟨64,199830433,199830545⟩]
theorem checked61848 : checkPrefixCuts (2^48) 8110473217 10 Manual.Count131072.C061848.packed 64 cuts61848 = true := by
 decide +kernel
def pointBounds61848 : List (Nat × Nat × Nat) := [(8110546944,114291250864169,114291639485641)]
theorem point_links_checked61848 : (cuts61848.take 1).map (fun c => (8110473217-1+2*2^10*c.k,114291137899539+c.lower,114291526520948+c.upper)) = pointBounds61848 := by
 decide +kernel
def cuts61849 : List PrefixCut := [⟨64,198612553,198612670⟩]
theorem checked61849 : checkPrefixCuts (2^48) 8110604289 10 Manual.Count131072.C061849.packed 64 cuts61849 = true := by
 decide +kernel
def cuts61850 : List PrefixCut := [⟨32,100190026,100190082⟩,
⟨64,202045010,202045122⟩]
theorem checked61850 : checkPrefixCuts (2^48) 8110735361 10 Manual.Count131072.C061850.packed 64 cuts61850 = true := by
 decide +kernel
def pointBounds61850 : List (Nat × Nat × Nat) := [(8110800896,114291636532551,114292025154245)]
theorem point_links_checked61850 : (cuts61850.take 1).map (fun c => (8110735361-1+2*2^10*c.k,114291536342525+c.lower,114291924964163+c.upper)) = pointBounds61850 := by
 decide +kernel
def cuts61851 : List PrefixCut := [⟨64,198120287,198120401⟩]
theorem checked61851 : checkPrefixCuts (2^48) 8110866433 10 Manual.Count131072.C061851.packed 64 cuts61851 = true := by
 decide +kernel
def cuts61852 : List PrefixCut := [⟨28,87971462,87971513⟩,
⟨64,198984653,198984763⟩]
theorem checked61852 : checkPrefixCuts (2^48) 8110997505 10 Manual.Count131072.C061852.packed 64 cuts61852 = true := by
 decide +kernel
def pointBounds61852 : List (Nat × Nat × Nat) := [(8111054848,114292024479284,114292413101199)]
theorem point_links_checked61852 : (cuts61852.take 1).map (fun c => (8110997505-1+2*2^10*c.k,114291936507822+c.lower,114292325129686+c.upper)) = pointBounds61852 := by
 decide +kernel
def cuts61853 : List PrefixCut := [⟨64,197246340,197246458⟩]
theorem checked61853 : checkPrefixCuts (2^48) 8111128577 10 Manual.Count131072.C061853.packed 64 cuts61853 = true := by
 decide +kernel
def cuts61854 : List PrefixCut := [⟨24,72908153,72908198⟩,
⟨64,196930822,196930939⟩]
theorem checked61854 : checkPrefixCuts (2^48) 8111259649 10 Manual.Count131072.C061854.packed 64 cuts61854 = true := by
 decide +kernel
def pointBounds61854 : List (Nat × Nat × Nat) := [(8111308800,114292405646968,114292794269105)]
theorem point_links_checked61854 : (cuts61854.take 1).map (fun c => (8111259649-1+2*2^10*c.k,114292332738815+c.lower,114292721360907+c.upper)) = pointBounds61854 := by
 decide +kernel
def cuts61855 : List PrefixCut := [⟨64,200501847,200501958⟩]
theorem checked61855 : checkPrefixCuts (2^48) 8111390721 10 Manual.Count131072.C061855.packed 64 cuts61855 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000057
