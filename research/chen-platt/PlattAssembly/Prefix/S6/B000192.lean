import PlattAssemblyKernel
import PlattCertificates.Count131072.C056144
import PlattCertificates.Count131072.C056145
import PlattCertificates.Count131072.C056146
import PlattCertificates.Count131072.C056147
import PlattCertificates.Count131072.C056148
import PlattCertificates.Count131072.C056149
import PlattCertificates.Count131072.C056150
import PlattCertificates.Count131072.C056151
import PlattCertificates.Count131072.C056152
import PlattCertificates.Count131072.C056153
import PlattCertificates.Count131072.C056154
import PlattCertificates.Count131072.C056155
import PlattCertificates.Count131072.C056156
import PlattCertificates.Count131072.C056157
import PlattCertificates.Count131072.C056158
import PlattCertificates.Count131072.C056159
import PlattCertificates.Count131072.C056160
import PlattCertificates.Count131072.C056161
import PlattCertificates.Count131072.C056162
import PlattCertificates.Count131072.C056163
import PlattCertificates.Count131072.C056164
import PlattCertificates.Count131072.C056165
import PlattCertificates.Count131072.C056166
import PlattCertificates.Count131072.C056167
import PlattCertificates.Count131072.C056168
import PlattCertificates.Count131072.C056169
import PlattCertificates.Count131072.C056170
import PlattCertificates.Count131072.C056171
import PlattCertificates.Count131072.C056172
import PlattCertificates.Count131072.C056173
import PlattCertificates.Count131072.C056174
import PlattCertificates.Count131072.C056175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56144 : List PrefixCut := [⟨11,36661678,36661698⟩,
⟨64,219471487,219471609⟩]
theorem checked56144 : checkPrefixCuts (2^48) 7362838529 10 Manual.Count131072.C056144.packed 64 cuts56144 = true := by
 decide +kernel
def pointBounds56144 : List (Nat × Nat × Nat) := [(7362861056,113095563318640,113095951258094)]
theorem point_links_checked56144 : (cuts56144.take 1).map (fun c => (7362838529-1+2*2^10*c.k,113095526656962+c.lower,113095914596396+c.upper)) = pointBounds56144 := by
 decide +kernel
def cuts56145 : List PrefixCut := [⟨60,207578736,207578855⟩,
⟨64,221646562,221646688⟩]
theorem checked56145 : checkPrefixCuts (2^48) 7362969601 10 Manual.Count131072.C056145.packed 64 cuts56145 = true := by
 decide +kernel
def pointBounds56145 : List (Nat × Nat × Nat) := [(7363092480,113095953707185,113096341646860)]
theorem point_links_checked56145 : (cuts56145.take 1).map (fun c => (7362969601-1+2*2^10*c.k,113095746128449+c.lower,113096134068005+c.upper)) = pointBounds56145 := by
 decide +kernel
def cuts56146 : List PrefixCut := [⟨64,220534021,220534149⟩]
theorem checked56146 : checkPrefixCuts (2^48) 7363100673 10 Manual.Count131072.C056146.packed 64 cuts56146 = true := by
 decide +kernel
def cuts56147 : List PrefixCut := [⟨45,155850861,155850948⟩,
⟨64,222020945,222021069⟩]
theorem checked56147 : checkPrefixCuts (2^48) 7363231745 10 Manual.Count131072.C056147.packed 64 cuts56147 = true := by
 decide +kernel
def pointBounds56147 : List (Nat × Nat × Nat) := [(7363323904,113096344159893,113096732099790)]
theorem point_links_checked56147 : (cuts56147.take 1).map (fun c => (7363231745-1+2*2^10*c.k,113096188309032+c.lower,113096576248842+c.upper)) = pointBounds56147 := by
 decide +kernel
def cuts56148 : List PrefixCut := [⟨64,221787621,221787746⟩]
theorem checked56148 : checkPrefixCuts (2^48) 7363362817 10 Manual.Count131072.C056148.packed 64 cuts56148 = true := by
 decide +kernel
def cuts56149 : List PrefixCut := [⟨30,104164662,104164720⟩,
⟨64,221592557,221592683⟩]
theorem checked56149 : checkPrefixCuts (2^48) 7363493889 10 Manual.Count131072.C056149.packed 64 cuts56149 = true := by
 decide +kernel
def pointBounds56149 : List (Nat × Nat × Nat) := [(7363555328,113096736282260,113097124222377)]
theorem point_links_checked56149 : (cuts56149.take 1).map (fun c => (7363493889-1+2*2^10*c.k,113096632117598+c.lower,113097020057657+c.upper)) = pointBounds56149 := by
 decide +kernel
def cuts56150 : List PrefixCut := [⟨64,223117630,223117755⟩]
theorem checked56150 : checkPrefixCuts (2^48) 7363624961 10 Manual.Count131072.C056150.packed 64 cuts56150 = true := by
 decide +kernel
def cuts56151 : List PrefixCut := [⟨15,52481942,52481972⟩,
⟨64,221775796,221775925⟩]
theorem checked56151 : checkPrefixCuts (2^48) 7363756033 10 Manual.Count131072.C056151.packed 64 cuts56151 = true := by
 decide +kernel
def pointBounds56151 : List (Nat × Nat × Nat) := [(7363786752,113097129309727,113097517250067)]
theorem point_links_checked56151 : (cuts56151.take 1).map (fun c => (7363756033-1+2*2^10*c.k,113097076827785+c.lower,113097464768095+c.upper)) = pointBounds56151 := by
 decide +kernel
def cuts56152 : List PrefixCut := [⟨64,218637531,218637657⟩]
theorem checked56152 : checkPrefixCuts (2^48) 7363887105 10 Manual.Count131072.C056152.packed 64 cuts56152 = true := by
 decide +kernel
def pointBounds56152 : List (Nat × Nat × Nat) := [(7364018176,113097517241112,113097905181677)]
theorem point_links_checked56152 : (cuts56152.take 1).map (fun c => (7363887105-1+2*2^10*c.k,113097298603581+c.lower,113097686544020+c.upper)) = pointBounds56152 := by
 decide +kernel
def cuts56153 : List PrefixCut := [⟨64,219971429,219971551⟩]
theorem checked56153 : checkPrefixCuts (2^48) 7364018177 10 Manual.Count131072.C056153.packed 64 cuts56153 = true := by
 decide +kernel
def cuts56154 : List PrefixCut := [⟨49,169094407,169094501⟩,
⟨64,221458167,221458290⟩]
theorem checked56154 : checkPrefixCuts (2^48) 7364149249 10 Manual.Count131072.C056154.packed 64 cuts56154 = true := by
 decide +kernel
def pointBounds56154 : List (Nat × Nat × Nat) := [(7364249600,113097906306948,113098294247729)]
theorem point_links_checked56154 : (cuts56154.take 1).map (fun c => (7364149249-1+2*2^10*c.k,113097737212541+c.lower,113098125153228+c.upper)) = pointBounds56154 := by
 decide +kernel
def cuts56155 : List PrefixCut := [⟨64,221683555,221683679⟩]
theorem checked56155 : checkPrefixCuts (2^48) 7364280321 10 Manual.Count131072.C056155.packed 64 cuts56155 = true := by
 decide +kernel
def cuts56156 : List PrefixCut := [⟨34,115770744,115770809⟩,
⟨64,221412039,221412163⟩]
theorem checked56156 : checkPrefixCuts (2^48) 7364411393 10 Manual.Count131072.C056156.packed 64 cuts56156 = true := by
 decide +kernel
def pointBounds56156 : List (Nat × Nat × Nat) := [(7364481024,113098296125007,113098684066006)]
theorem point_links_checked56156 : (cuts56156.take 1).map (fun c => (7364411393-1+2*2^10*c.k,113098180354263+c.lower,113098568295197+c.upper)) = pointBounds56156 := by
 decide +kernel
def cuts56157 : List PrefixCut := [⟨64,217930092,217930219⟩]
theorem checked56157 : checkPrefixCuts (2^48) 7364542465 10 Manual.Count131072.C056157.packed 64 cuts56157 = true := by
 decide +kernel
def cuts56158 : List PrefixCut := [⟨19,66005082,66005116⟩,
⟨64,222130358,222130479⟩]
theorem checked56158 : checkPrefixCuts (2^48) 7364673537 10 Manual.Count131072.C056158.packed 64 cuts56158 = true := by
 decide +kernel
def pointBounds56158 : List (Nat × Nat × Nat) := [(7364712448,113098685701476,113099073642695)]
theorem point_links_checked56158 : (cuts56158.take 1).map (fun c => (7364673537-1+2*2^10*c.k,113098619696394+c.lower,113099007637579+c.upper)) = pointBounds56158 := by
 decide +kernel
def cuts56159 : List PrefixCut := [⟨64,220024362,220024490⟩]
theorem checked56159 : checkPrefixCuts (2^48) 7364804609 10 Manual.Count131072.C056159.packed 64 cuts56159 = true := by
 decide +kernel
def cuts56160 : List PrefixCut := [⟨4,13338159,13338167⟩,
⟨64,220364429,220364555⟩]
theorem checked56160 : checkPrefixCuts (2^48) 7364935681 10 Manual.Count131072.C056160.packed 64 cuts56160 = true := by
 decide +kernel
def pointBounds56160 : List (Nat × Nat × Nat) := [(7364943872,113099075189273,113099463130715)]
theorem point_links_checked56160 : (cuts56160.take 1).map (fun c => (7364935681-1+2*2^10*c.k,113099061851114+c.lower,113099449792548+c.upper)) = pointBounds56160 := by
 decide +kernel
def cuts56161 : List PrefixCut := [⟨53,180309136,180309239⟩,
⟨64,219290414,219290539⟩]
theorem checked56161 : checkPrefixCuts (2^48) 7365066753 10 Manual.Count131072.C056161.packed 64 cuts56161 = true := by
 decide +kernel
def pointBounds56161 : List (Nat × Nat × Nat) := [(7365175296,113099462524679,113099850466342)]
theorem point_links_checked56161 : (cuts56161.take 1).map (fun c => (7365066753-1+2*2^10*c.k,113099282215543+c.lower,113099670157103+c.upper)) = pointBounds56161 := by
 decide +kernel
def cuts56162 : List PrefixCut := [⟨64,219439378,219439505⟩]
theorem checked56162 : checkPrefixCuts (2^48) 7365197825 10 Manual.Count131072.C056162.packed 64 cuts56162 = true := by
 decide +kernel
def cuts56163 : List PrefixCut := [⟨38,131654116,131654190⟩,
⟨64,220085153,220085278⟩]
theorem checked56163 : checkPrefixCuts (2^48) 7365328897 10 Manual.Count131072.C056163.packed 64 cuts56163 = true := by
 decide +kernel
def pointBounds56163 : List (Nat × Nat × Nat) := [(7365406720,113099852599451,113100240541337)]
theorem point_links_checked56163 : (cuts56163.take 1).map (fun c => (7365328897-1+2*2^10*c.k,113099720945335+c.lower,113100108887147+c.upper)) = pointBounds56163 := by
 decide +kernel
def cuts56164 : List PrefixCut := [⟨64,221036614,221036739⟩]
theorem checked56164 : checkPrefixCuts (2^48) 7365459969 10 Manual.Count131072.C056164.packed 64 cuts56164 = true := by
 decide +kernel
def cuts56165 : List PrefixCut := [⟨23,78913393,78913439⟩,
⟨64,221223751,221223878⟩]
theorem checked56165 : checkPrefixCuts (2^48) 7365591041 10 Manual.Count131072.C056165.packed 64 cuts56165 = true := by
 decide +kernel
def pointBounds56165 : List (Nat × Nat × Nat) := [(7365638144,113100240980495,113100628922603)]
theorem point_links_checked56165 : (cuts56165.take 1).map (fun c => (7365591041-1+2*2^10*c.k,113100162067102+c.lower,113100550009164+c.upper)) = pointBounds56165 := by
 decide +kernel
def cuts56166 : List PrefixCut := [⟨64,218583069,218583194⟩]
theorem checked56166 : checkPrefixCuts (2^48) 7365722113 10 Manual.Count131072.C056166.packed 64 cuts56166 = true := by
 decide +kernel
def cuts56167 : List PrefixCut := [⟨8,26711195,26711211⟩,
⟨64,219419856,219419983⟩]
theorem checked56167 : checkPrefixCuts (2^48) 7365853185 10 Manual.Count131072.C056167.packed 64 cuts56167 = true := by
 decide +kernel
def pointBounds56167 : List (Nat × Nat × Nat) := [(7365869568,113100628585117,113101016527447)]
theorem point_links_checked56167 : (cuts56167.take 1).map (fun c => (7365853185-1+2*2^10*c.k,113100601873922+c.lower,113100989816236+c.upper)) = pointBounds56167 := by
 decide +kernel
def cuts56168 : List PrefixCut := [⟨57,194883742,194883851⟩,
⟨64,218154946,218155068⟩]
theorem checked56168 : checkPrefixCuts (2^48) 7365984257 10 Manual.Count131072.C056168.packed 64 cuts56168 = true := by
 decide +kernel
def pointBounds56168 : List (Nat × Nat × Nat) := [(7366100992,113101016177520,113101404120070)]
theorem point_links_checked56168 : (cuts56168.take 1).map (fun c => (7365984257-1+2*2^10*c.k,113100821293778+c.lower,113101209236219+c.upper)) = pointBounds56168 := by
 decide +kernel
def cuts56169 : List PrefixCut := [⟨64,219908802,219908926⟩]
theorem checked56169 : checkPrefixCuts (2^48) 7366115329 10 Manual.Count131072.C056169.packed 64 cuts56169 = true := by
 decide +kernel
def cuts56170 : List PrefixCut := [⟨42,146196121,146196202⟩,
⟨64,222082924,222083050⟩]
theorem checked56170 : checkPrefixCuts (2^48) 7366246401 10 Manual.Count131072.C056170.packed 64 cuts56170 = true := by
 decide +kernel
def pointBounds56170 : List (Nat × Nat × Nat) := [(7366332416,113101405553647,113101793496415)]
theorem point_links_checked56170 : (cuts56170.take 1).map (fun c => (7366246401-1+2*2^10*c.k,113101259357526+c.lower,113101647300213+c.upper)) = pointBounds56170 := by
 decide +kernel
def cuts56171 : List PrefixCut := [⟨64,220015595,220015719⟩]
theorem checked56171 : checkPrefixCuts (2^48) 7366377473 10 Manual.Count131072.C056171.packed 64 cuts56171 = true := by
 decide +kernel
def cuts56172 : List PrefixCut := [⟨27,90442925,90442974⟩,
⟨64,219247492,219247615⟩]
theorem checked56172 : checkPrefixCuts (2^48) 7366508545 10 Manual.Count131072.C056172.packed 64 cuts56172 = true := by
 decide +kernel
def pointBounds56172 : List (Nat × Nat × Nat) := [(7366563840,113101791898970,113102179841956)]
theorem point_links_checked56172 : (cuts56172.take 1).map (fun c => (7366508545-1+2*2^10*c.k,113101701456045+c.lower,113102089398982+c.upper)) = pointBounds56172 := by
 decide +kernel
def cuts56173 : List PrefixCut := [⟨64,215537328,215537452⟩]
theorem checked56173 : checkPrefixCuts (2^48) 7366639617 10 Manual.Count131072.C056173.packed 64 cuts56173 = true := by
 decide +kernel
def cuts56174 : List PrefixCut := [⟨12,40271925,40271949⟩,
⟨64,219889246,219889371⟩]
theorem checked56174 : checkPrefixCuts (2^48) 7366770689 10 Manual.Count131072.C056174.packed 64 cuts56174 = true := by
 decide +kernel
def pointBounds56174 : List (Nat × Nat × Nat) := [(7366795264,113102176512790,113102564455998)]
theorem point_links_checked56174 : (cuts56174.take 1).map (fun c => (7366770689-1+2*2^10*c.k,113102136240865+c.lower,113102524184049+c.upper)) = pointBounds56174 := by
 decide +kernel
def cuts56175 : List PrefixCut := [⟨61,208575935,208576053⟩,
⟨64,218204195,218204318⟩]
theorem checked56175 : checkPrefixCuts (2^48) 7366901761 10 Manual.Count131072.C056175.packed 64 cuts56175 = true := by
 decide +kernel
def pointBounds56175 : List (Nat × Nat × Nat) := [(7367026688,113102564706046,113102952649473)]
theorem point_links_checked56175 : (cuts56175.take 1).map (fun c => (7366901761-1+2*2^10*c.k,113102356130111+c.lower,113102744073420+c.upper)) = pointBounds56175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000192
