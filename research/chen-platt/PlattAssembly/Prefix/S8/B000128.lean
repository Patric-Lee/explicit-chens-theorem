import PlattAssemblyKernel
import PlattCertificates.Count131072.C074096
import PlattCertificates.Count131072.C074097
import PlattCertificates.Count131072.C074098
import PlattCertificates.Count131072.C074099
import PlattCertificates.Count131072.C074100
import PlattCertificates.Count131072.C074101
import PlattCertificates.Count131072.C074102
import PlattCertificates.Count131072.C074103
import PlattCertificates.Count131072.C074104
import PlattCertificates.Count131072.C074105
import PlattCertificates.Count131072.C074106
import PlattCertificates.Count131072.C074107
import PlattCertificates.Count131072.C074108
import PlattCertificates.Count131072.C074109
import PlattCertificates.Count131072.C074110
import PlattCertificates.Count131072.C074111
import PlattCertificates.Count131072.C074112
import PlattCertificates.Count131072.C074113
import PlattCertificates.Count131072.C074114
import PlattCertificates.Count131072.C074115
import PlattCertificates.Count131072.C074116
import PlattCertificates.Count131072.C074117
import PlattCertificates.Count131072.C074118
import PlattCertificates.Count131072.C074119
import PlattCertificates.Count131072.C074120
import PlattCertificates.Count131072.C074121
import PlattCertificates.Count131072.C074122
import PlattCertificates.Count131072.C074123
import PlattCertificates.Count131072.C074124
import PlattCertificates.Count131072.C074125
import PlattCertificates.Count131072.C074126
import PlattCertificates.Count131072.C074127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74096 : List PrefixCut := [⟨28,72281711,72281754⟩,
⟨64,164146946,164147048⟩]
theorem checked74096 : checkPrefixCuts (2^48) 9715843073 10 Manual.Count131072.C074096.packed 64 cuts74096 = true := by
 decide +kernel
def pointBounds74096 : List (Nat × Nat × Nat) := [(9715900416,116510481710258,116510871628817)]
theorem point_links_checked74096 : (cuts74096.take 1).map (fun c => (9715843073-1+2*2^10*c.k,116510409428547+c.lower,116510799347063+c.upper)) = pointBounds74096 := by
 decide +kernel
def cuts74097 : List PrefixCut := [⟨64,165013851,165013943⟩]
theorem checked74097 : checkPrefixCuts (2^48) 9715974145 10 Manual.Count131072.C074097.packed 64 cuts74097 = true := by
 decide +kernel
def cuts74098 : List PrefixCut := [⟨49,124975629,124975709⟩,
⟨64,162085670,162085772⟩]
theorem checked74098 : checkPrefixCuts (2^48) 9716105217 10 Manual.Count131072.C074098.packed 64 cuts74098 = true := by
 decide +kernel
def pointBounds74098 : List (Nat × Nat × Nat) := [(9716205568,116510863564973,116511253483763)]
theorem point_links_checked74098 : (cuts74098.take 1).map (fun c => (9716105217-1+2*2^10*c.k,116510738589344+c.lower,116511128508054+c.upper)) = pointBounds74098 := by
 decide +kernel
def cuts74099 : List PrefixCut := [⟨64,165820527,165820630⟩]
theorem checked74099 : checkPrefixCuts (2^48) 9716236289 10 Manual.Count131072.C074099.packed 64 cuts74099 = true := by
 decide +kernel
def cuts74100 : List PrefixCut := [⟨64,165354778,165354881⟩]
theorem checked74100 : checkPrefixCuts (2^48) 9716367361 10 Manual.Count131072.C074100.packed 64 cuts74100 = true := by
 decide +kernel
def cuts74101 : List PrefixCut := [⟨6,15092714,15092723⟩,
⟨64,163121980,163122083⟩]
theorem checked74101 : checkPrefixCuts (2^48) 9716498433 10 Manual.Count131072.C074101.packed 64 cuts74101 = true := by
 decide +kernel
def pointBounds74101 : List (Nat × Nat × Nat) := [(9716510720,116511246943033,116511636862060)]
theorem point_links_checked74101 : (cuts74101.take 1).map (fun c => (9716498433-1+2*2^10*c.k,116511231850319+c.lower,116511621769337+c.upper)) = pointBounds74101 := by
 decide +kernel
def cuts74102 : List PrefixCut := [⟨64,166045562,166045659⟩]
theorem checked74102 : checkPrefixCuts (2^48) 9716629505 10 Manual.Count131072.C074102.packed 64 cuts74102 = true := by
 decide +kernel
def cuts74103 : List PrefixCut := [⟨27,69870560,69870606⟩,
⟨64,163696937,163697036⟩]
theorem checked74103 : checkPrefixCuts (2^48) 9716760577 10 Manual.Count131072.C074103.packed 64 cuts74103 = true := by
 decide +kernel
def pointBounds74103 : List (Nat × Nat × Nat) := [(9716815872,116511630888421,116512020807685)]
theorem point_links_checked74103 : (cuts74103.take 1).map (fun c => (9716760577-1+2*2^10*c.k,116511561017861+c.lower,116511950937079+c.upper)) = pointBounds74103 := by
 decide +kernel
def cuts74104 : List PrefixCut := [⟨64,166562482,166562582⟩]
theorem checked74104 : checkPrefixCuts (2^48) 9716891649 10 Manual.Count131072.C074104.packed 64 cuts74104 = true := by
 decide +kernel
def cuts74105 : List PrefixCut := [⟨48,122704414,122704487⟩,
⟨64,163229040,163229138⟩]
theorem checked74105 : checkPrefixCuts (2^48) 9717022721 10 Manual.Count131072.C074105.packed 64 cuts74105 = true := by
 decide +kernel
def pointBounds74105 : List (Nat × Nat × Nat) := [(9717121024,116512013981694,116512403901184)]
theorem point_links_checked74105 : (cuts74105.take 1).map (fun c => (9717022721-1+2*2^10*c.k,116511891277280+c.lower,116512281196697+c.upper)) = pointBounds74105 := by
 decide +kernel
def cuts74106 : List PrefixCut := [⟨64,163661348,163661445⟩]
theorem checked74106 : checkPrefixCuts (2^48) 9717153793 10 Manual.Count131072.C074106.packed 64 cuts74106 = true := by
 decide +kernel
def cuts74107 : List PrefixCut := [⟨64,165628852,165628949⟩]
theorem checked74107 : checkPrefixCuts (2^48) 9717284865 10 Manual.Count131072.C074107.packed 64 cuts74107 = true := by
 decide +kernel
def cuts74108 : List PrefixCut := [⟨5,12831942,12831949⟩,
⟨64,162527259,162527364⟩]
theorem checked74108 : checkPrefixCuts (2^48) 9717415937 10 Manual.Count131072.C074108.packed 64 cuts74108 = true := by
 decide +kernel
def pointBounds74108 : List (Nat × Nat × Nat) := [(9717426176,116512396628462,116512786548178)]
theorem point_links_checked74108 : (cuts74108.take 1).map (fun c => (9717415937-1+2*2^10*c.k,116512383796520+c.lower,116512773716229+c.upper)) = pointBounds74108 := by
 decide +kernel
def cuts74109 : List PrefixCut := [⟨64,165363672,165363775⟩]
theorem checked74109 : checkPrefixCuts (2^48) 9717547009 10 Manual.Count131072.C074109.packed 64 cuts74109 = true := by
 decide +kernel
def cuts74110 : List PrefixCut := [⟨26,66504010,66504052⟩,
⟨64,165795916,165796015⟩]
theorem checked74110 : checkPrefixCuts (2^48) 9717678081 10 Manual.Count131072.C074110.packed 64 cuts74110 = true := by
 decide +kernel
def pointBounds74110 : List (Nat × Nat × Nat) := [(9717731328,116512778191461,116513168111420)]
theorem point_links_checked74110 : (cuts74110.take 1).map (fun c => (9717678081-1+2*2^10*c.k,116512711687451+c.lower,116513101607368+c.upper)) = pointBounds74110 := by
 decide +kernel
def cuts74111 : List PrefixCut := [⟨64,167241916,167242019⟩]
theorem checked74111 : checkPrefixCuts (2^48) 9717809153 10 Manual.Count131072.C074111.packed 64 cuts74111 = true := by
 decide +kernel
def cuts74112 : List PrefixCut := [⟨47,122576992,122577062⟩,
⟨64,165936281,165936377⟩]
theorem checked74112 : checkPrefixCuts (2^48) 9717940225 10 Manual.Count131072.C074112.packed 64 cuts74112 = true := by
 decide +kernel
def pointBounds74112 : List (Nat × Nat × Nat) := [(9718036480,116513167302275,116513557222464)]
theorem point_links_checked74112 : (cuts74112.take 1).map (fun c => (9717940225-1+2*2^10*c.k,116513044725283+c.lower,116513434645402+c.upper)) = pointBounds74112 := by
 decide +kernel
def cuts74113 : List PrefixCut := [⟨64,164167235,164167338⟩]
theorem checked74113 : checkPrefixCuts (2^48) 9718071297 10 Manual.Count131072.C074113.packed 64 cuts74113 = true := by
 decide +kernel
def cuts74114 : List PrefixCut := [⟨64,165902835,165902934⟩]
theorem checked74114 : checkPrefixCuts (2^48) 9718202369 10 Manual.Count131072.C074114.packed 64 cuts74114 = true := by
 decide +kernel
def cuts74115 : List PrefixCut := [⟨4,9644771,9644777⟩,
⟨64,167232892,167232990⟩]
theorem checked74115 : checkPrefixCuts (2^48) 9718333441 10 Manual.Count131072.C074115.packed 64 cuts74115 = true := by
 decide +kernel
def pointBounds74115 : List (Nat × Nat × Nat) := [(9718341632,116513550376405,116513940296828)]
theorem point_links_checked74115 : (cuts74115.take 1).map (fun c => (9718333441-1+2*2^10*c.k,116513540731634+c.lower,116513930652051+c.upper)) = pointBounds74115 := by
 decide +kernel
def cuts74116 : List PrefixCut := [⟨64,162654541,162654639⟩]
theorem checked74116 : checkPrefixCuts (2^48) 9718464513 10 Manual.Count131072.C074116.packed 64 cuts74116 = true := by
 decide +kernel
def cuts74117 : List PrefixCut := [⟨25,64557258,64557297⟩,
⟨64,164911400,164911504⟩]
theorem checked74117 : checkPrefixCuts (2^48) 9718595585 10 Manual.Count131072.C074117.packed 64 cuts74117 = true := by
 decide +kernel
def pointBounds74117 : List (Nat × Nat × Nat) := [(9718646784,116513935176325,116514325096977)]
theorem point_links_checked74117 : (cuts74117.take 1).map (fun c => (9718595585-1+2*2^10*c.k,116513870619067+c.lower,116514260539680+c.upper)) = pointBounds74117 := by
 decide +kernel
def cuts74118 : List PrefixCut := [⟨64,164445788,164445889⟩]
theorem checked74118 : checkPrefixCuts (2^48) 9718726657 10 Manual.Count131072.C074118.packed 64 cuts74118 = true := by
 decide +kernel
def cuts74119 : List PrefixCut := [⟨46,118829386,118829461⟩,
⟨64,165370342,165370444⟩]
theorem checked74119 : checkPrefixCuts (2^48) 9718857729 10 Manual.Count131072.C074119.packed 64 cuts74119 = true := by
 decide +kernel
def pointBounds74119 : List (Nat × Nat × Nat) := [(9718951936,116514318805641,116514708726534)]
theorem point_links_checked74119 : (cuts74119.take 1).map (fun c => (9718857729-1+2*2^10*c.k,116514199976255+c.lower,116514589897073+c.upper)) = pointBounds74119 := by
 decide +kernel
def cuts74120 : List PrefixCut := [⟨64,167858770,167858869⟩]
theorem checked74120 : checkPrefixCuts (2^48) 9718988801 10 Manual.Count131072.C074120.packed 64 cuts74120 = true := by
 decide +kernel
def cuts74121 : List PrefixCut := [⟨64,165423802,165423898⟩]
theorem checked74121 : checkPrefixCuts (2^48) 9719119873 10 Manual.Count131072.C074121.packed 64 cuts74121 = true := by
 decide +kernel
def cuts74122 : List PrefixCut := [⟨3,8224794,8224800⟩,
⟨64,164726527,164726623⟩]
theorem checked74122 : checkPrefixCuts (2^48) 9719250945 10 Manual.Count131072.C074122.packed 64 cuts74122 = true := by
 decide +kernel
def pointBounds74122 : List (Nat × Nat × Nat) := [(9719257088,116514706853963,116515096775084)]
theorem point_links_checked74122 : (cuts74122.take 1).map (fun c => (9719250945-1+2*2^10*c.k,116514698629169+c.lower,116515088550284+c.upper)) = pointBounds74122 := by
 decide +kernel
def cuts74123 : List PrefixCut := [⟨64,163479034,163479125⟩]
theorem checked74123 : checkPrefixCuts (2^48) 9719382017 10 Manual.Count131072.C074123.packed 64 cuts74123 = true := by
 decide +kernel
def cuts74124 : List PrefixCut := [⟨24,62929430,62929469⟩,
⟨64,165330236,165330334⟩]
theorem checked74124 : checkPrefixCuts (2^48) 9719513089 10 Manual.Count131072.C074124.packed 64 cuts74124 = true := by
 decide +kernel
def pointBounds74124 : List (Nat × Nat × Nat) := [(9719562240,116515089764160,116515479685501)]
theorem point_links_checked74124 : (cuts74124.take 1).map (fun c => (9719513089-1+2*2^10*c.k,116515026834730+c.lower,116515416756032+c.upper)) = pointBounds74124 := by
 decide +kernel
def cuts74125 : List PrefixCut := [⟨64,164893618,164893715⟩]
theorem checked74125 : checkPrefixCuts (2^48) 9719644161 10 Manual.Count131072.C074125.packed 64 cuts74125 = true := by
 decide +kernel
def cuts74126 : List PrefixCut := [⟨45,116848978,116849044⟩,
⟨64,165731196,165731288⟩]
theorem checked74126 : checkPrefixCuts (2^48) 9719775233 10 Manual.Count131072.C074126.packed 64 cuts74126 = true := by
 decide +kernel
def pointBounds74126 : List (Nat × Nat × Nat) := [(9719867392,116515473907562,116515863829125)]
theorem point_links_checked74126 : (cuts74126.take 1).map (fun c => (9719775233-1+2*2^10*c.k,116515357058584+c.lower,116515746980081+c.upper)) = pointBounds74126 := by
 decide +kernel
def cuts74127 : List PrefixCut := [⟨64,165149795,165149891⟩]
theorem checked74127 : checkPrefixCuts (2^48) 9719906305 10 Manual.Count131072.C074127.packed 64 cuts74127 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000128
