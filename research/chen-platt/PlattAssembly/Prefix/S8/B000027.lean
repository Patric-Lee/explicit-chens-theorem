import PlattAssemblyKernel
import PlattCertificates.Count131072.C070864
import PlattCertificates.Count131072.C070865
import PlattCertificates.Count131072.C070866
import PlattCertificates.Count131072.C070867
import PlattCertificates.Count131072.C070868
import PlattCertificates.Count131072.C070869
import PlattCertificates.Count131072.C070870
import PlattCertificates.Count131072.C070871
import PlattCertificates.Count131072.C070872
import PlattCertificates.Count131072.C070873
import PlattCertificates.Count131072.C070874
import PlattCertificates.Count131072.C070875
import PlattCertificates.Count131072.C070876
import PlattCertificates.Count131072.C070877
import PlattCertificates.Count131072.C070878
import PlattCertificates.Count131072.C070879
import PlattCertificates.Count131072.C070880
import PlattCertificates.Count131072.C070881
import PlattCertificates.Count131072.C070882
import PlattCertificates.Count131072.C070883
import PlattCertificates.Count131072.C070884
import PlattCertificates.Count131072.C070885
import PlattCertificates.Count131072.C070886
import PlattCertificates.Count131072.C070887
import PlattCertificates.Count131072.C070888
import PlattCertificates.Count131072.C070889
import PlattCertificates.Count131072.C070890
import PlattCertificates.Count131072.C070891
import PlattCertificates.Count131072.C070892
import PlattCertificates.Count131072.C070893
import PlattCertificates.Count131072.C070894
import PlattCertificates.Count131072.C070895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70864 : List PrefixCut := [⟨64,170933533,170933632⟩]
theorem checked70864 : checkPrefixCuts (2^48) 9292218369 10 Manual.Count131072.C070864.packed 64 cuts70864 = true := by
 decide +kernel
def cuts70865 : List PrefixCut := [⟨61,166569289,166569386⟩,
⟨64,174717465,174717567⟩]
theorem checked70865 : checkPrefixCuts (2^48) 9292349441 10 Manual.Count131072.C070865.packed 64 cuts70865 = true := by
 decide +kernel
def pointBounds70865 : List (Nat × Nat × Nat) := [(9292474368,115964532722672,115964922316710)]
theorem point_links_checked70865 : (cuts70865.take 1).map (fun c => (9292349441-1+2*2^10*c.k,115964366153383+c.lower,115964755747324+c.upper)) = pointBounds70865 := by
 decide +kernel
def cuts70866 : List PrefixCut := [⟨64,173109595,173109704⟩]
theorem checked70866 : checkPrefixCuts (2^48) 9292480513 10 Manual.Count131072.C070866.packed 64 cuts70866 = true := by
 decide +kernel
def cuts70867 : List PrefixCut := [⟨64,172380211,172380312⟩]
theorem checked70867 : checkPrefixCuts (2^48) 9292611585 10 Manual.Count131072.C070867.packed 64 cuts70867 = true := by
 decide +kernel
def cuts70868 : List PrefixCut := [⟨11,29229578,29229596⟩,
⟨64,173771099,173771206⟩]
theorem checked70868 : checkPrefixCuts (2^48) 9292742657 10 Manual.Count131072.C070868.packed 64 cuts70868 = true := by
 decide +kernel
def pointBounds70868 : List (Nat × Nat × Nat) := [(9292765184,115964915590232,115965305184503)]
theorem point_links_checked70868 : (cuts70868.take 1).map (fun c => (9292742657-1+2*2^10*c.k,115964886360654+c.lower,115965275954907+c.upper)) = pointBounds70868 := by
 decide +kernel
def cuts70869 : List PrefixCut := [⟨64,173798925,173799028⟩]
theorem checked70869 : checkPrefixCuts (2^48) 9292873729 10 Manual.Count131072.C070869.packed 64 cuts70869 = true := by
 decide +kernel
def cuts70870 : List PrefixCut := [⟨25,66544531,66544570⟩,
⟨64,171494545,171494645⟩]
theorem checked70870 : checkPrefixCuts (2^48) 9293004801 10 Manual.Count131072.C070870.packed 64 cuts70870 = true := by
 decide +kernel
def pointBounds70870 : List (Nat × Nat × Nat) := [(9293056000,115965300475209,115965690069711)]
theorem point_links_checked70870 : (cuts70870.take 1).map (fun c => (9293004801-1+2*2^10*c.k,115965233930678+c.lower,115965623525141+c.upper)) = pointBounds70870 := by
 decide +kernel
def cuts70871 : List PrefixCut := [⟨64,173945475,173945574⟩]
theorem checked70871 : checkPrefixCuts (2^48) 9293135873 10 Manual.Count131072.C070871.packed 64 cuts70871 = true := by
 decide +kernel
def cuts70872 : List PrefixCut := [⟨39,107249516,107249579⟩,
⟨64,175487706,175487811⟩]
theorem checked70872 : checkPrefixCuts (2^48) 9293266945 10 Manual.Count131072.C070872.packed 64 cuts70872 = true := by
 decide +kernel
def pointBounds70872 : List (Nat × Nat × Nat) := [(9293346816,115965686620214,115966076214939)]
theorem point_links_checked70872 : (cuts70872.take 1).map (fun c => (9293266945-1+2*2^10*c.k,115965579370698+c.lower,115965968965360+c.upper)) = pointBounds70872 := by
 decide +kernel
def cuts70873 : List PrefixCut := [⟨64,173819408,173819507⟩]
theorem checked70873 : checkPrefixCuts (2^48) 9293398017 10 Manual.Count131072.C070873.packed 64 cuts70873 = true := by
 decide +kernel
def cuts70874 : List PrefixCut := [⟨53,140138018,140138104⟩,
⟨64,169879656,169879761⟩]
theorem checked70874 : checkPrefixCuts (2^48) 9293529089 10 Manual.Count131072.C070874.packed 64 cuts70874 = true := by
 decide +kernel
def pointBounds70874 : List (Nat × Nat × Nat) := [(9293637632,115966068815830,115966458410782)]
theorem point_links_checked70874 : (cuts70874.take 1).map (fun c => (9293529089-1+2*2^10*c.k,115965928677812+c.lower,115966318272678+c.upper)) = pointBounds70874 := by
 decide +kernel
def cuts70875 : List PrefixCut := [⟨64,173057347,173057448⟩]
theorem checked70875 : checkPrefixCuts (2^48) 9293660161 10 Manual.Count131072.C070875.packed 64 cuts70875 = true := by
 decide +kernel
def cuts70876 : List PrefixCut := [⟨64,170753153,170753254⟩]
theorem checked70876 : checkPrefixCuts (2^48) 9293791233 10 Manual.Count131072.C070876.packed 64 cuts70876 = true := by
 decide +kernel
def cuts70877 : List PrefixCut := [⟨3,7965192,7965196⟩,
⟨64,172840461,172840560⟩]
theorem checked70877 : checkPrefixCuts (2^48) 9293922305 10 Manual.Count131072.C070877.packed 64 cuts70877 = true := by
 decide +kernel
def pointBounds70877 : List (Nat × Nat × Nat) := [(9293928448,115966450333160,115966839928337)]
theorem point_links_checked70877 : (cuts70877.take 1).map (fun c => (9293922305-1+2*2^10*c.k,115966442367968+c.lower,115966831963141+c.upper)) = pointBounds70877 := by
 decide +kernel
def cuts70878 : List PrefixCut := [⟨64,175775700,175775803⟩]
theorem checked70878 : checkPrefixCuts (2^48) 9294053377 10 Manual.Count131072.C070878.packed 64 cuts70878 = true := by
 decide +kernel
def cuts70879 : List PrefixCut := [⟨17,44640089,44640117⟩,
⟨64,173108151,173108251⟩]
theorem checked70879 : checkPrefixCuts (2^48) 9294184449 10 Manual.Count131072.C070879.packed 64 cuts70879 = true := by
 decide +kernel
def pointBounds70879 : List (Nat × Nat × Nat) := [(9294219264,115966835624218,115967225219621)]
theorem point_links_checked70879 : (cuts70879.take 1).map (fun c => (9294184449-1+2*2^10*c.k,115966790984129+c.lower,115967180579504+c.upper)) = pointBounds70879 := by
 decide +kernel
def cuts70880 : List PrefixCut := [⟨64,172257756,172257853⟩]
theorem checked70880 : checkPrefixCuts (2^48) 9294315521 10 Manual.Count131072.C070880.packed 64 cuts70880 = true := by
 decide +kernel
def cuts70881 : List PrefixCut := [⟨31,82736153,82736199⟩,
⟨64,171649640,171649740⟩]
theorem checked70881 : checkPrefixCuts (2^48) 9294446593 10 Manual.Count131072.C070881.packed 64 cuts70881 = true := by
 decide +kernel
def pointBounds70881 : List (Nat × Nat × Nat) := [(9294510080,115967219086189,115967608681807)]
theorem point_links_checked70881 : (cuts70881.take 1).map (fun c => (9294446593-1+2*2^10*c.k,115967136350036+c.lower,115967525945608+c.upper)) = pointBounds70881 := by
 decide +kernel
def cuts70882 : List PrefixCut := [⟨64,170072471,170072573⟩]
theorem checked70882 : checkPrefixCuts (2^48) 9294577665 10 Manual.Count131072.C070882.packed 64 cuts70882 = true := by
 decide +kernel
def cuts70883 : List PrefixCut := [⟨45,121920155,121920227⟩,
⟨64,172432171,172432274⟩]
theorem checked70883 : checkPrefixCuts (2^48) 9294708737 10 Manual.Count131072.C070883.packed 64 cuts70883 = true := by
 decide +kernel
def pointBounds70883 : List (Nat × Nat × Nat) := [(9294800896,115967599992302,115967989588148)]
theorem point_links_checked70883 : (cuts70883.take 1).map (fun c => (9294708737-1+2*2^10*c.k,115967478072147+c.lower,115967867667921+c.upper)) = pointBounds70883 := by
 decide +kernel
def cuts70884 : List PrefixCut := [⟨64,171793794,171793900⟩]
theorem checked70884 : checkPrefixCuts (2^48) 9294839809 10 Manual.Count131072.C070884.packed 64 cuts70884 = true := by
 decide +kernel
def cuts70885 : List PrefixCut := [⟨59,158194710,158194809⟩,
⟨64,171700518,171700626⟩]
theorem checked70885 : checkPrefixCuts (2^48) 9294970881 10 Manual.Count131072.C070885.packed 64 cuts70885 = true := by
 decide +kernel
def pointBounds70885 : List (Nat × Nat × Nat) := [(9295091712,115967980492822,115968370088904)]
theorem point_links_checked70885 : (cuts70885.take 1).map (fun c => (9294970881-1+2*2^10*c.k,115967822298112+c.lower,115968211894095+c.upper)) = pointBounds70885 := by
 decide +kernel
def cuts70886 : List PrefixCut := [⟨64,172031205,172031305⟩]
theorem checked70886 : checkPrefixCuts (2^48) 9295101953 10 Manual.Count131072.C070886.packed 64 cuts70886 = true := by
 decide +kernel
def cuts70887 : List PrefixCut := [⟨64,174330172,174330271⟩]
theorem checked70887 : checkPrefixCuts (2^48) 9295233025 10 Manual.Count131072.C070887.packed 64 cuts70887 = true := by
 decide +kernel
def cuts70888 : List PrefixCut := [⟨9,24527757,24527772⟩,
⟨64,173025631,173025732⟩]
theorem checked70888 : checkPrefixCuts (2^48) 9295364097 10 Manual.Count131072.C070888.packed 64 cuts70888 = true := by
 decide +kernel
def pointBounds70888 : List (Nat × Nat × Nat) := [(9295382528,115968364887764,115968754484069)]
theorem point_links_checked70888 : (cuts70888.take 1).map (fun c => (9295364097-1+2*2^10*c.k,115968340360007+c.lower,115968729956297+c.upper)) = pointBounds70888 := by
 decide +kernel
def cuts70889 : List PrefixCut := [⟨64,174567499,174567608⟩]
theorem checked70889 : checkPrefixCuts (2^48) 9295495169 10 Manual.Count131072.C070889.packed 64 cuts70889 = true := by
 decide +kernel
def cuts70890 : List PrefixCut := [⟨23,62528781,62528817⟩,
⟨64,172445431,172445526⟩]
theorem checked70890 : checkPrefixCuts (2^48) 9295626241 10 Manual.Count131072.C070890.packed 64 cuts70890 = true := by
 decide +kernel
def pointBounds70890 : List (Nat × Nat × Nat) := [(9295673344,115968750481918,115969140078454)]
theorem point_links_checked70890 : (cuts70890.take 1).map (fun c => (9295626241-1+2*2^10*c.k,115968687953137+c.lower,115969077549637+c.upper)) = pointBounds70890 := by
 decide +kernel
def cuts70891 : List PrefixCut := [⟨64,171807133,171807229⟩]
theorem checked70891 : checkPrefixCuts (2^48) 9295757313 10 Manual.Count131072.C070891.packed 64 cuts70891 = true := by
 decide +kernel
def cuts70892 : List PrefixCut := [⟨37,102344302,102344366⟩,
⟨64,175771280,175771391⟩]
theorem checked70892 : checkPrefixCuts (2^48) 9295888385 10 Manual.Count131072.C070892.packed 64 cuts70892 = true := by
 decide +kernel
def pointBounds70892 : List (Nat × Nat × Nat) := [(9295964160,115969134550003,115969524146758)]
theorem point_links_checked70892 : (cuts70892.take 1).map (fun c => (9295888385-1+2*2^10*c.k,115969032205701+c.lower,115969421802392+c.upper)) = pointBounds70892 := by
 decide +kernel
def cuts70893 : List PrefixCut := [⟨64,175526571,175526674⟩]
theorem checked70893 : checkPrefixCuts (2^48) 9296019457 10 Manual.Count131072.C070893.packed 64 cuts70893 = true := by
 decide +kernel
def cuts70894 : List PrefixCut := [⟨51,137282632,137282714⟩,
⟨64,173495441,173495540⟩]
theorem checked70894 : checkPrefixCuts (2^48) 9296150529 10 Manual.Count131072.C070894.packed 64 cuts70894 = true := by
 decide +kernel
def pointBounds70894 : List (Nat × Nat × Nat) := [(9296254976,115969520786184,115969910383171)]
theorem point_links_checked70894 : (cuts70894.take 1).map (fun c => (9296150529-1+2*2^10*c.k,115969383503552+c.lower,115969773100457+c.upper)) = pointBounds70894 := by
 decide +kernel
def cuts70895 : List PrefixCut := [⟨64,171312976,171313076⟩]
theorem checked70895 : checkPrefixCuts (2^48) 9296281601 10 Manual.Count131072.C070895.packed 64 cuts70895 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000027
