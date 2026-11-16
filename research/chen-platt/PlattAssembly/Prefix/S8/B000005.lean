import PlattAssemblyKernel
import PlattCertificates.Count131072.C070160
import PlattCertificates.Count131072.C070161
import PlattCertificates.Count131072.C070162
import PlattCertificates.Count131072.C070163
import PlattCertificates.Count131072.C070164
import PlattCertificates.Count131072.C070165
import PlattCertificates.Count131072.C070166
import PlattCertificates.Count131072.C070167
import PlattCertificates.Count131072.C070168
import PlattCertificates.Count131072.C070169
import PlattCertificates.Count131072.C070170
import PlattCertificates.Count131072.C070171
import PlattCertificates.Count131072.C070172
import PlattCertificates.Count131072.C070173
import PlattCertificates.Count131072.C070174
import PlattCertificates.Count131072.C070175
import PlattCertificates.Count131072.C070176
import PlattCertificates.Count131072.C070177
import PlattCertificates.Count131072.C070178
import PlattCertificates.Count131072.C070179
import PlattCertificates.Count131072.C070180
import PlattCertificates.Count131072.C070181
import PlattCertificates.Count131072.C070182
import PlattCertificates.Count131072.C070183
import PlattCertificates.Count131072.C070184
import PlattCertificates.Count131072.C070185
import PlattCertificates.Count131072.C070186
import PlattCertificates.Count131072.C070187
import PlattCertificates.Count131072.C070188
import PlattCertificates.Count131072.C070189
import PlattCertificates.Count131072.C070190
import PlattCertificates.Count131072.C070191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70160 : List PrefixCut := [⟨24,66238616,66238651⟩,
⟨64,175891043,175891143⟩]
theorem checked70160 : checkPrefixCuts (2^48) 9199943681 10 Manual.Count131072.C070160.packed 64 cuts70160 = true := by
 decide +kernel
def pointBounds70160 : List (Nat × Nat × Nat) := [(9199992832,115841762435770,115842151957405)]
theorem point_links_checked70160 : (cuts70160.take 1).map (fun c => (9199943681-1+2*2^10*c.k,115841696197154+c.lower,115842085718754+c.upper)) = pointBounds70160 := by
 decide +kernel
def cuts70161 : List PrefixCut := [⟨64,174175223,174175334⟩]
theorem checked70161 : checkPrefixCuts (2^48) 9200074753 10 Manual.Count131072.C070161.packed 64 cuts70161 = true := by
 decide +kernel
def cuts70162 : List PrefixCut := [⟨37,103041554,103041618⟩,
⟨64,175886030,175886142⟩]
theorem checked70162 : checkPrefixCuts (2^48) 9200205825 10 Manual.Count131072.C070162.packed 64 cuts70162 = true := by
 decide +kernel
def pointBounds70162 : List (Nat × Nat × Nat) := [(9200281600,115842149304974,115842538826849)]
theorem point_links_checked70162 : (cuts70162.take 1).map (fun c => (9200205825-1+2*2^10*c.k,115842046263420+c.lower,115842435785231+c.upper)) = pointBounds70162 := by
 decide +kernel
def cuts70163 : List PrefixCut := [⟨64,174904523,174904627⟩]
theorem checked70163 : checkPrefixCuts (2^48) 9200336897 10 Manual.Count131072.C070163.packed 64 cuts70163 = true := by
 decide +kernel
def cuts70164 : List PrefixCut := [⟨50,135467449,135467527⟩,
⟨64,174259566,174259670⟩]
theorem checked70164 : checkPrefixCuts (2^48) 9200467969 10 Manual.Count131072.C070164.packed 64 cuts70164 = true := by
 decide +kernel
def pointBounds70164 : List (Nat × Nat × Nat) := [(9200570368,115842532521422,115842922043527)]
theorem point_links_checked70164 : (cuts70164.take 1).map (fun c => (9200467969-1+2*2^10*c.k,115842397053973+c.lower,115842786576000+c.upper)) = pointBounds70164 := by
 decide +kernel
def cuts70165 : List PrefixCut := [⟨64,175358422,175358530⟩]
theorem checked70165 : checkPrefixCuts (2^48) 9200599041 10 Manual.Count131072.C070165.packed 64 cuts70165 = true := by
 decide +kernel
def cuts70166 : List PrefixCut := [⟨63,171684853,171684952⟩,
⟨64,174438154,174438255⟩]
theorem checked70166 : checkPrefixCuts (2^48) 9200730113 10 Manual.Count131072.C070166.packed 64 cuts70166 = true := by
 decide +kernel
def pointBounds70166 : List (Nat × Nat × Nat) := [(9200859136,115842918356814,115843307879152)]
theorem point_links_checked70166 : (cuts70166.take 1).map (fun c => (9200730113-1+2*2^10*c.k,115842746671961+c.lower,115843136194200+c.upper)) = pointBounds70166 := by
 decide +kernel
def cuts70167 : List PrefixCut := [⟨64,173793247,173793345⟩]
theorem checked70167 : checkPrefixCuts (2^48) 9200861185 10 Manual.Count131072.C070167.packed 64 cuts70167 = true := by
 decide +kernel
def cuts70168 : List PrefixCut := [⟨64,175809810,175809911⟩]
theorem checked70168 : checkPrefixCuts (2^48) 9200992257 10 Manual.Count131072.C070168.packed 64 cuts70168 = true := by
 decide +kernel
def cuts70169 : List PrefixCut := [⟨12,32610351,32610367⟩,
⟨64,172595245,172595345⟩]
theorem checked70169 : checkPrefixCuts (2^48) 9201123329 10 Manual.Count131072.C070169.packed 64 cuts70169 = true := by
 decide +kernel
def pointBounds70169 : List (Nat × Nat × Nat) := [(9201147904,115843303323523,115843692846078)]
theorem point_links_checked70169 : (cuts70169.take 1).map (fun c => (9201123329-1+2*2^10*c.k,115843270713172+c.lower,115843660235711+c.upper)) = pointBounds70169 := by
 decide +kernel
def cuts70170 : List PrefixCut := [⟨64,174336453,174336553⟩]
theorem checked70170 : checkPrefixCuts (2^48) 9201254401 10 Manual.Count131072.C070170.packed 64 cuts70170 = true := by
 decide +kernel
def cuts70171 : List PrefixCut := [⟨25,68063651,68063695⟩,
⟨64,173385666,173385777⟩]
theorem checked70171 : checkPrefixCuts (2^48) 9201385473 10 Manual.Count131072.C070171.packed 64 cuts70171 = true := by
 decide +kernel
def pointBounds70171 : List (Nat × Nat × Nat) := [(9201436672,115843685708521,115844075231304)]
theorem point_links_checked70171 : (cuts70171.take 1).map (fun c => (9201385473-1+2*2^10*c.k,115843617644870+c.lower,115844007167609+c.upper)) = pointBounds70171 := by
 decide +kernel
def cuts70172 : List PrefixCut := [⟨64,174270310,174270414⟩]
theorem checked70172 : checkPrefixCuts (2^48) 9201516545 10 Manual.Count131072.C070172.packed 64 cuts70172 = true := by
 decide +kernel
def cuts70173 : List PrefixCut := [⟨38,105197247,105197311⟩,
⟨64,177051445,177051550⟩]
theorem checked70173 : checkPrefixCuts (2^48) 9201647617 10 Manual.Count131072.C070173.packed 64 cuts70173 = true := by
 decide +kernel
def pointBounds70173 : List (Nat × Nat × Nat) := [(9201725440,115844070498093,115844460021111)]
theorem point_links_checked70173 : (cuts70173.take 1).map (fun c => (9201647617-1+2*2^10*c.k,115843965300846+c.lower,115844354823800+c.upper)) = pointBounds70173 := by
 decide +kernel
def cuts70174 : List PrefixCut := [⟨64,172582949,172583054⟩]
theorem checked70174 : checkPrefixCuts (2^48) 9201778689 10 Manual.Count131072.C070174.packed 64 cuts70174 = true := by
 decide +kernel
def cuts70175 : List PrefixCut := [⟨51,139667432,139667517⟩,
⟨64,175364046,175364150⟩]
theorem checked70175 : checkPrefixCuts (2^48) 9201909761 10 Manual.Count131072.C070175.packed 64 cuts70175 = true := by
 decide +kernel
def pointBounds70175 : List (Nat × Nat × Nat) := [(9202014208,115844454602672,115844844125921)]
theorem point_links_checked70175 : (cuts70175.take 1).map (fun c => (9201909761-1+2*2^10*c.k,115844314935240+c.lower,115844704458404+c.upper)) = pointBounds70175 := by
 decide +kernel
def cuts70176 : List PrefixCut := [⟨64,177013302,177013405⟩]
theorem checked70176 : checkPrefixCuts (2^48) 9202040833 10 Manual.Count131072.C070176.packed 64 cuts70176 = true := by
 decide +kernel
def cuts70177 : List PrefixCut := [⟨64,175542566,175542669⟩]
theorem checked70177 : checkPrefixCuts (2^48) 9202171905 10 Manual.Count131072.C070177.packed 64 cuts70177 = true := by
 decide +kernel
def pointBounds70177 : List (Nat × Nat × Nat) := [(9202302976,115844842855154,115845232378628)]
theorem point_links_checked70177 : (cuts70177.take 1).map (fun c => (9202171905-1+2*2^10*c.k,115844667312588+c.lower,115845056835959+c.upper)) = pointBounds70177 := by
 decide +kernel
def cuts70178 : List PrefixCut := [⟨64,177283547,177283653⟩]
theorem checked70178 : checkPrefixCuts (2^48) 9202302977 10 Manual.Count131072.C070178.packed 64 cuts70178 = true := by
 decide +kernel
def cuts70179 : List PrefixCut := [⟨64,175170540,175170640⟩]
theorem checked70179 : checkPrefixCuts (2^48) 9202434049 10 Manual.Count131072.C070179.packed 64 cuts70179 = true := by
 decide +kernel
def cuts70180 : List PrefixCut := [⟨13,36887350,36887372⟩,
⟨64,175902124,175902229⟩]
theorem checked70180 : checkPrefixCuts (2^48) 9202565121 10 Manual.Count131072.C070180.packed 64 cuts70180 = true := by
 decide +kernel
def pointBounds70180 : List (Nat × Nat × Nat) := [(9202591744,115845232196591,115845621720293)]
theorem point_links_checked70180 : (cuts70180.take 1).map (fun c => (9202565121-1+2*2^10*c.k,115845195309241+c.lower,115845584832921+c.upper)) = pointBounds70180 := by
 decide +kernel
def cuts70181 : List PrefixCut := [⟨64,175196136,175196239⟩]
theorem checked70181 : checkPrefixCuts (2^48) 9202696193 10 Manual.Count131072.C070181.packed 64 cuts70181 = true := by
 decide +kernel
def cuts70182 : List PrefixCut := [⟨26,72090280,72090326⟩,
⟨64,175866514,175866618⟩]
theorem checked70182 : checkPrefixCuts (2^48) 9202827265 10 Manual.Count131072.C070182.packed 64 cuts70182 = true := by
 decide +kernel
def pointBounds70182 : List (Nat × Nat × Nat) := [(9202880512,115845618497781,115846008021715)]
theorem point_links_checked70182 : (cuts70182.take 1).map (fun c => (9202827265-1+2*2^10*c.k,115845546407501+c.lower,115845935931389+c.upper)) = pointBounds70182 := by
 decide +kernel
def cuts70183 : List PrefixCut := [⟨64,174273581,174273689⟩]
theorem checked70183 : checkPrefixCuts (2^48) 9202958337 10 Manual.Count131072.C070183.packed 64 cuts70183 = true := by
 decide +kernel
def cuts70184 : List PrefixCut := [⟨39,104416147,104416204⟩,
⟨64,174821614,174821709⟩]
theorem checked70184 : checkPrefixCuts (2^48) 9203089409 10 Manual.Count131072.C070184.packed 64 cuts70184 = true := by
 decide +kernel
def pointBounds70184 : List (Nat × Nat × Nat) := [(9203169280,115846000963743,115846390487900)]
theorem point_links_checked70184 : (cuts70184.take 1).map (fun c => (9203089409-1+2*2^10*c.k,115845896547596+c.lower,115846286071696+c.upper)) = pointBounds70184 := by
 decide +kernel
def cuts70185 : List PrefixCut := [⟨64,177174113,177174218⟩]
theorem checked70185 : checkPrefixCuts (2^48) 9203220481 10 Manual.Count131072.C070185.packed 64 cuts70185 = true := by
 decide +kernel
def cuts70186 : List PrefixCut := [⟨52,141113556,141113638⟩,
⟨64,174174385,174174487⟩]
theorem checked70186 : checkPrefixCuts (2^48) 9203351553 10 Manual.Count131072.C070186.packed 64 cuts70186 = true := by
 decide +kernel
def pointBounds70186 : List (Nat × Nat × Nat) := [(9203458048,115846389656879,115846779181261)]
theorem point_links_checked70186 : (cuts70186.take 1).map (fun c => (9203351553-1+2*2^10*c.k,115846248543323+c.lower,115846638067623+c.upper)) = pointBounds70186 := by
 decide +kernel
def cuts70187 : List PrefixCut := [⟨64,173621407,173621502⟩]
theorem checked70187 : checkPrefixCuts (2^48) 9203482625 10 Manual.Count131072.C070187.packed 64 cuts70187 = true := by
 decide +kernel
def cuts70188 : List PrefixCut := [⟨64,173985934,173986033⟩]
theorem checked70188 : checkPrefixCuts (2^48) 9203613697 10 Manual.Count131072.C070188.packed 64 cuts70188 = true := by
 decide +kernel
def cuts70189 : List PrefixCut := [⟨1,2538360,2538361⟩,
⟨64,173861126,173861227⟩]
theorem checked70189 : checkPrefixCuts (2^48) 9203744769 10 Manual.Count131072.C070189.packed 64 cuts70189 = true := by
 decide +kernel
def pointBounds70189 : List (Nat × Nat × Nat) := [(9203746816,115846772863409,115847162388006)]
theorem point_links_checked70189 : (cuts70189.take 1).map (fun c => (9203744769-1+2*2^10*c.k,115846770325049+c.lower,115847159849645+c.upper)) = pointBounds70189 := by
 decide +kernel
def cuts70190 : List PrefixCut := [⟨64,174592617,174592717⟩]
theorem checked70190 : checkPrefixCuts (2^48) 9203875841 10 Manual.Count131072.C070190.packed 64 cuts70190 = true := by
 decide +kernel
def cuts70191 : List PrefixCut := [⟨14,36789821,36789843⟩,
⟨64,174926506,174926613⟩]
theorem checked70191 : checkPrefixCuts (2^48) 9204006913 10 Manual.Count131072.C070191.packed 64 cuts70191 = true := by
 decide +kernel
def pointBounds70191 : List (Nat × Nat × Nat) := [(9204035584,115847155568613,115847545093432)]
theorem point_links_checked70191 : (cuts70191.take 1).map (fun c => (9204006913-1+2*2^10*c.k,115847118778792+c.lower,115847508303589+c.upper)) = pointBounds70191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000005
