import PlattAssemblyKernel
import PlattCertificates.Count131072.C026144
import PlattCertificates.Count131072.C026145
import PlattCertificates.Count131072.C026146
import PlattCertificates.Count131072.C026147
import PlattCertificates.Count131072.C026148
import PlattCertificates.Count131072.C026149
import PlattCertificates.Count131072.C026150
import PlattCertificates.Count131072.C026151
import PlattCertificates.Count131072.C026152
import PlattCertificates.Count131072.C026153
import PlattCertificates.Count131072.C026154
import PlattCertificates.Count131072.C026155
import PlattCertificates.Count131072.C026156
import PlattCertificates.Count131072.C026157
import PlattCertificates.Count131072.C026158
import PlattCertificates.Count131072.C026159
import PlattCertificates.Count131072.C026160
import PlattCertificates.Count131072.C026161
import PlattCertificates.Count131072.C026162
import PlattCertificates.Count131072.C026163
import PlattCertificates.Count131072.C026164
import PlattCertificates.Count131072.C026165
import PlattCertificates.Count131072.C026166
import PlattCertificates.Count131072.C026167
import PlattCertificates.Count131072.C026168
import PlattCertificates.Count131072.C026169
import PlattCertificates.Count131072.C026170
import PlattCertificates.Count131072.C026171
import PlattCertificates.Count131072.C026172
import PlattCertificates.Count131072.C026173
import PlattCertificates.Count131072.C026174
import PlattCertificates.Count131072.C026175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000192
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26144 : List PrefixCut := [⟨58,220128649,220128774⟩,
⟨128,484474891,484475170⟩]
theorem checked26144 : checkPrefixCuts (2^48) 3430678529 9 Manual.Count131072.C026144.packed 128 cuts26144 = true := by
 decide +kernel
def pointBounds26144 : List (Nat × Nat × Nat) := [(3430737920,103471749931515,103472132269493)]
theorem point_links_checked26144 : (cuts26144.take 1).map (fun c => (3430678529-1+2*2^9*c.k,103471529802866+c.lower,103471912140719+c.upper)) = pointBounds26144 := by
 decide +kernel
def cuts26145 : List PrefixCut := [⟨35,132827381,132827454⟩,
⟨128,494629492,494629765⟩]
theorem checked26145 : checkPrefixCuts (2^48) 3430809601 9 Manual.Count131072.C026145.packed 128 cuts26145 = true := by
 decide +kernel
def pointBounds26145 : List (Nat × Nat × Nat) := [(3430845440,103472147105138,103472529443343)]
theorem point_links_checked26145 : (cuts26145.take 1).map (fun c => (3430809601-1+2*2^9*c.k,103472014277757+c.lower,103472396615889+c.upper)) = pointBounds26145 := by
 decide +kernel
def cuts26146 : List PrefixCut := [⟨12,47993404,47993430⟩,
⟨117,442927101,442927348⟩,
⟨128,484766051,484766321⟩]
theorem checked26146 : checkPrefixCuts (2^48) 3430940673 9 Manual.Count131072.C026146.packed 128 cuts26146 = true := by
 decide +kernel
def pointBounds26146 : List (Nat × Nat × Nat) := [(3430952960,103472556900653,103472939239084),(3431060480,103472951834350,103473334173002)]
theorem point_links_checked26146 : (cuts26146.take 2).map (fun c => (3430940673-1+2*2^9*c.k,103472508907249+c.lower,103472891245654+c.upper)) = pointBounds26146 := by
 decide +kernel
def cuts26147 : List PrefixCut := [⟨94,366208149,366208354⟩,
⟨128,495986401,495986681⟩]
theorem checked26147 : checkPrefixCuts (2^48) 3431071745 9 Manual.Count131072.C026147.packed 128 cuts26147 = true := by
 decide +kernel
def pointBounds26147 : List (Nat × Nat × Nat) := [(3431168000,103473359881449,103473742220329)]
theorem point_links_checked26147 : (cuts26147.take 1).map (fun c => (3431071745-1+2*2^9*c.k,103472993673300+c.lower,103473376011975+c.upper)) = pointBounds26147 := by
 decide +kernel
def cuts26148 : List PrefixCut := [⟨71,276451236,276451393⟩,
⟨128,495803329,495803607⟩]
theorem checked26148 : checkPrefixCuts (2^48) 3431202817 9 Manual.Count131072.C026148.packed 128 cuts26148 = true := by
 decide +kernel
def pointBounds26148 : List (Nat × Nat × Nat) := [(3431275520,103473766110937,103474148450049)]
theorem point_links_checked26148 : (cuts26148.take 1).map (fun c => (3431202817-1+2*2^9*c.k,103473489659701+c.lower,103473871998656+c.upper)) = pointBounds26148 := by
 decide +kernel
def cuts26149 : List PrefixCut := [⟨48,183009288,183009395⟩,
⟨128,481019162,481019436⟩]
theorem checked26149 : checkPrefixCuts (2^48) 3431333889 9 Manual.Count131072.C026149.packed 128 cuts26149 = true := by
 decide +kernel
def pointBounds26149 : List (Nat × Nat × Nat) := [(3431383040,103474168472318,103474550811658)]
theorem point_links_checked26149 : (cuts26149.take 1).map (fun c => (3431333889-1+2*2^9*c.k,103473985463030+c.lower,103474367802263+c.upper)) = pointBounds26149 := by
 decide +kernel
def cuts26150 : List PrefixCut := [⟨25,96464116,96464170⟩,
⟨128,492730473,492730752⟩]
theorem checked26150 : checkPrefixCuts (2^48) 3431464961 9 Manual.Count131072.C026150.packed 128 cuts26150 = true := by
 decide +kernel
def pointBounds26150 : List (Nat × Nat × Nat) := [(3431490560,103474562946308,103474945285869)]
theorem point_links_checked26150 : (cuts26150.take 1).map (fun c => (3431464961-1+2*2^9*c.k,103474466482192+c.lower,103474848821699+c.upper)) = pointBounds26150 := by
 decide +kernel
def cuts26151 : List PrefixCut := [⟨2,7628275,7628279⟩,
⟨107,402241669,402241892⟩,
⟨128,483607111,483607381⟩]
theorem checked26151 : checkPrefixCuts (2^48) 3431596033 9 Manual.Count131072.C026151.packed 128 cuts26151 = true := by
 decide +kernel
def pointBounds26151 : List (Nat × Nat × Nat) := [(3431598080,103474966840940,103475349180730),(3431705600,103475361454334,103475743794343)]
theorem point_links_checked26151 : (cuts26151.take 2).map (fun c => (3431596033-1+2*2^9*c.k,103474959212665+c.lower,103475341552451+c.upper)) = pointBounds26151 := by
 decide +kernel
def cuts26152 : List PrefixCut := [⟨84,320453431,320453609⟩,
⟨128,486705459,486705734⟩]
theorem checked26152 : checkPrefixCuts (2^48) 3431727105 9 Manual.Count131072.C026152.packed 128 cuts26152 = true := by
 decide +kernel
def pointBounds26152 : List (Nat × Nat × Nat) := [(3431813120,103475763273207,103476145613441)]
theorem point_links_checked26152 : (cuts26152.take 1).map (fun c => (3431727105-1+2*2^9*c.k,103475442819776+c.lower,103475825159832+c.upper)) = pointBounds26152 := by
 decide +kernel
def cuts26153 : List PrefixCut := [⟨61,232683534,232683663⟩,
⟨128,489967449,489967724⟩]
theorem checked26153 : checkPrefixCuts (2^48) 3431858177 9 Manual.Count131072.C026153.packed 128 cuts26153 = true := by
 decide +kernel
def pointBounds26153 : List (Nat × Nat × Nat) := [(3431920640,103476162208769,103476544549229)]
theorem point_links_checked26153 : (cuts26153.take 1).map (fun c => (3431858177-1+2*2^9*c.k,103475929525235+c.lower,103476311865566+c.upper)) = pointBounds26153 := by
 decide +kernel
def cuts26154 : List PrefixCut := [⟨38,145575934,145576018⟩,
⟨128,488800599,488800876⟩]
theorem checked26154 : checkPrefixCuts (2^48) 3431989249 9 Manual.Count131072.C026154.packed 128 cuts26154 = true := by
 decide +kernel
def pointBounds26154 : List (Nat × Nat × Nat) := [(3432028160,103476565068618,103476947409308)]
theorem point_links_checked26154 : (cuts26154.take 1).map (fun c => (3431989249-1+2*2^9*c.k,103476419492684+c.lower,103476801833290+c.upper)) = pointBounds26154 := by
 decide +kernel
def cuts26155 : List PrefixCut := [⟨15,58228354,58228385⟩,
⟨120,461801091,461801349⟩,
⟨128,493046490,493046767⟩]
theorem checked26155 : checkPrefixCuts (2^48) 3432120321 9 Manual.Count131072.C026155.packed 128 cuts26155 = true := by
 decide +kernel
def pointBounds26155 : List (Nat × Nat × Nat) := [(3432135680,103476966521637,103477348862551),(3432243200,103477370094374,103477752435515)]
theorem point_links_checked26155 : (cuts26155.take 2).map (fun c => (3432120321-1+2*2^9*c.k,103476908293283+c.lower,103477290634166+c.upper)) = pointBounds26155 := by
 decide +kernel
def cuts26156 : List PrefixCut := [⟨97,367968300,367968508⟩,
⟨128,485236981,485237259⟩]
theorem checked26156 : checkPrefixCuts (2^48) 3432251393 9 Manual.Count131072.C026156.packed 128 cuts26156 = true := by
 decide +kernel
def pointBounds26156 : List (Nat × Nat × Nat) := [(3432350720,103477769308073,103478151649441)]
theorem point_links_checked26156 : (cuts26156.take 1).map (fun c => (3432251393-1+2*2^9*c.k,103477401339773+c.lower,103477783680933+c.upper)) = pointBounds26156 := by
 decide +kernel
def cuts26157 : List PrefixCut := [⟨74,283900559,283900720⟩,
⟨128,489974642,489974916⟩]
theorem checked26157 : checkPrefixCuts (2^48) 3432382465 9 Manual.Count131072.C026157.packed 128 cuts26157 = true := by
 decide +kernel
def pointBounds26157 : List (Nat × Nat × Nat) := [(3432458240,103478170477313,103478552818912)]
theorem point_links_checked26157 : (cuts26157.take 1).map (fun c => (3432382465-1+2*2^9*c.k,103477886576754+c.lower,103478268918192+c.upper)) = pointBounds26157 := by
 decide +kernel
def cuts26158 : List PrefixCut := [⟨51,197624662,197624772⟩,
⟨128,493563975,493564253⟩]
theorem checked26158 : checkPrefixCuts (2^48) 3432513537 9 Manual.Count131072.C026158.packed 128 cuts26158 = true := by
 decide +kernel
def pointBounds26158 : List (Nat × Nat × Nat) := [(3432565760,103478574176058,103478956517880)]
theorem point_links_checked26158 : (cuts26158.take 1).map (fun c => (3432513537-1+2*2^9*c.k,103478376551396+c.lower,103478758893108+c.upper)) = pointBounds26158 := by
 decide +kernel
def cuts26159 : List PrefixCut := [⟨28,108730793,108730852⟩,
⟨128,490183313,490183589⟩]
theorem checked26159 : checkPrefixCuts (2^48) 3432644609 9 Manual.Count131072.C026159.packed 128 cuts26159 = true := by
 decide +kernel
def pointBounds26159 : List (Nat × Nat × Nat) := [(3432673280,103478978846164,103479361188213)]
theorem point_links_checked26159 : (cuts26159.take 1).map (fun c => (3432644609-1+2*2^9*c.k,103478870115371+c.lower,103479252457361+c.upper)) = pointBounds26159 := by
 decide +kernel
def cuts26160 : List PrefixCut := [⟨5,19023127,19023138⟩,
⟨110,421044108,421044339⟩,
⟨128,487786728,487786996⟩]
theorem checked26160 : checkPrefixCuts (2^48) 3432775681 9 Manual.Count131072.C026160.packed 128 cuts26160 = true := by
 decide +kernel
def pointBounds26160 : List (Nat × Nat × Nat) := [(3432780800,103479379321811,103479761664088),(3432888320,103479781342792,103480163685289)]
theorem point_links_checked26160 : (cuts26160.take 2).map (fun c => (3432775681-1+2*2^9*c.k,103479360298684+c.lower,103479742640950+c.upper)) = pointBounds26160 := by
 decide +kernel
def cuts26161 : List PrefixCut := [⟨87,333051918,333052109⟩,
⟨128,485718303,485718579⟩]
theorem checked26161 : checkPrefixCuts (2^48) 3432906753 9 Manual.Count131072.C026161.packed 128 cuts26161 = true := by
 decide +kernel
def pointBounds26161 : List (Nat × Nat × Nat) := [(3432995840,103480181137330,103480563480055)]
theorem point_links_checked26161 : (cuts26161.take 1).map (fun c => (3432906753-1+2*2^9*c.k,103479848085412+c.lower,103480230427946+c.upper)) = pointBounds26161 := by
 decide +kernel
def cuts26162 : List PrefixCut := [⟨64,244491990,244492127⟩,
⟨128,485699783,485700056⟩]
theorem checked26162 : checkPrefixCuts (2^48) 3433037825 9 Manual.Count131072.C026162.packed 128 cuts26162 = true := by
 decide +kernel
def pointBounds26162 : List (Nat × Nat × Nat) := [(3433103360,103480578295705,103480960638652)]
theorem point_links_checked26162 : (cuts26162.take 1).map (fun c => (3433037825-1+2*2^9*c.k,103480333803715+c.lower,103480716146525+c.upper)) = pointBounds26162 := by
 decide +kernel
def cuts26163 : List PrefixCut := [⟨41,155364236,155364320⟩,
⟨128,487648776,487649046⟩]
theorem checked26163 : checkPrefixCuts (2^48) 3433168897 9 Manual.Count131072.C026163.packed 128 cuts26163 = true := by
 decide +kernel
def pointBounds26163 : List (Nat × Nat × Nat) := [(3433210880,103480974867734,103481357210901)]
theorem point_links_checked26163 : (cuts26163.take 1).map (fun c => (3433168897-1+2*2^9*c.k,103480819503498+c.lower,103481201846581+c.upper)) = pointBounds26163 := by
 decide +kernel
def cuts26164 : List PrefixCut := [⟨18,69112142,69112178⟩,
⟨123,472791815,472792076⟩,
⟨128,491811338,491811610⟩]
theorem checked26164 : checkPrefixCuts (2^48) 3433299969 9 Manual.Count131072.C026164.packed 128 cuts26164 = true := by
 decide +kernel
def pointBounds26164 : List (Nat × Nat × Nat) := [(3433318400,103481376264416,103481758607805),(3433425920,103481779944089,103482162287703)]
theorem point_links_checked26164 : (cuts26164.take 2).map (fun c => (3433299969-1+2*2^9*c.k,103481307152274+c.lower,103481689495627+c.upper)) = pointBounds26164 := by
 decide +kernel
def cuts26165 : List PrefixCut := [⟨100,386287081,386287300⟩,
⟨128,491628624,491628904⟩]
theorem checked26165 : checkPrefixCuts (2^48) 3433431041 9 Manual.Count131072.C026165.packed 128 cuts26165 = true := by
 decide +kernel
def pointBounds26165 : List (Nat × Nat × Nat) := [(3433533440,103482185250693,103482567594537)]
theorem point_links_checked26165 : (cuts26165.take 1).map (fun c => (3433431041-1+2*2^9*c.k,103481798963612+c.lower,103482181307237+c.upper)) = pointBounds26165 := by
 decide +kernel
def cuts26166 : List PrefixCut := [⟨77,296099399,296099563⟩,
⟨128,491609791,491610066⟩]
theorem checked26166 : checkPrefixCuts (2^48) 3433562113 9 Manual.Count131072.C026166.packed 128 cuts26166 = true := by
 decide +kernel
def pointBounds26166 : List (Nat × Nat × Nat) := [(3433640960,103482586691635,103482969035704)]
theorem point_links_checked26166 : (cuts26166.take 1).map (fun c => (3433562113-1+2*2^9*c.k,103482290592236+c.lower,103482672936141+c.upper)) = pointBounds26166 := by
 decide +kernel
def cuts26167 : List PrefixCut := [⟨54,202557088,202557199⟩,
⟨128,484459365,484459633⟩]
theorem checked26167 : checkPrefixCuts (2^48) 3433693185 9 Manual.Count131072.C026167.packed 128 cuts26167 = true := by
 decide +kernel
def pointBounds26167 : List (Nat × Nat × Nat) := [(3433748480,103482984759115,103483367103406)]
theorem point_links_checked26167 : (cuts26167.take 1).map (fun c => (3433693185-1+2*2^9*c.k,103482782202027+c.lower,103483164546207+c.upper)) = pointBounds26167 := by
 decide +kernel
def cuts26168 : List PrefixCut := [⟨31,118611861,118611926⟩,
⟨128,489932836,489933110⟩]
theorem checked26168 : checkPrefixCuts (2^48) 3433824257 9 Manual.Count131072.C026168.packed 128 cuts26168 = true := by
 decide +kernel
def pointBounds26168 : List (Nat × Nat × Nat) := [(3433856000,103483385273253,103483767617766)]
theorem point_links_checked26168 : (cuts26168.take 1).map (fun c => (3433824257-1+2*2^9*c.k,103483266661392+c.lower,103483649005840+c.upper)) = pointBounds26168 := by
 decide +kernel
def cuts26169 : List PrefixCut := [⟨8,31393758,31393775⟩,
⟨113,428686182,428686417⟩,
⟨128,487701117,487701382⟩]
theorem checked26169 : checkPrefixCuts (2^48) 3433955329 9 Manual.Count131072.C026169.packed 128 cuts26169 = true := by
 decide +kernel
def pointBounds26169 : List (Nat × Nat × Nat) := [(3433963520,103483787987986,103484170332725),(3434071040,103484185280410,103484567625367)]
theorem point_links_checked26169 : (cuts26169.take 2).map (fun c => (3433955329-1+2*2^9*c.k,103483756594228+c.lower,103484138938950+c.upper)) = pointBounds26169 := by
 decide +kernel
def cuts26170 : List PrefixCut := [⟨90,339248579,339248774⟩,
⟨128,485387444,485387720⟩]
theorem checked26170 : checkPrefixCuts (2^48) 3434086401 9 Manual.Count131072.C026170.packed 128 cuts26170 = true := by
 decide +kernel
def pointBounds26170 : List (Nat × Nat × Nat) := [(3434178560,103484583543924,103484965889106)]
theorem point_links_checked26170 : (cuts26170.take 1).map (fun c => (3434086401-1+2*2^9*c.k,103484244295345+c.lower,103484626640332+c.upper)) = pointBounds26170 := by
 decide +kernel
def cuts26171 : List PrefixCut := [⟨67,259324756,259324900⟩,
⟨128,489303089,489303365⟩]
theorem checked26171 : checkPrefixCuts (2^48) 3434217473 9 Manual.Count131072.C026171.packed 128 cuts26171 = true := by
 decide +kernel
def pointBounds26171 : List (Nat × Nat × Nat) := [(3434286080,103484989007545,103485371352952)]
theorem point_links_checked26171 : (cuts26171.take 1).map (fun c => (3434217473-1+2*2^9*c.k,103484729682789+c.lower,103485112028052+c.upper)) = pointBounds26171 := by
 decide +kernel
def cuts26172 : List PrefixCut := [⟨44,169653502,169653592⟩,
⟨128,488382896,488383161⟩]
theorem checked26172 : checkPrefixCuts (2^48) 3434348545 9 Manual.Count131072.C026172.packed 128 cuts26172 = true := by
 decide +kernel
def pointBounds26172 : List (Nat × Nat × Nat) := [(3434393600,103485388639380,103485770985009)]
theorem point_links_checked26172 : (cuts26172.take 1).map (fun c => (3434348545-1+2*2^9*c.k,103485218985878+c.lower,103485601331417+c.upper)) = pointBounds26172 := by
 decide +kernel
def cuts26173 : List PrefixCut := [⟨21,76792174,76792216⟩,
⟨126,474186231,474186501⟩,
⟨128,481561958,481562232⟩]
theorem checked26173 : checkPrefixCuts (2^48) 3434479617 9 Manual.Count131072.C026173.packed 128 cuts26173 = true := by
 decide +kernel
def pointBounds26173 : List (Nat × Nat × Nat) := [(3434501120,103485784160948,103486166506794),(3434608640,103486181555005,103486563901079)]
theorem point_links_checked26173 : (cuts26173.take 2).map (fun c => (3434479617-1+2*2^9*c.k,103485707368774+c.lower,103486089714578+c.upper)) = pointBounds26173 := by
 decide +kernel
def cuts26174 : List PrefixCut := [⟨103,399840064,399840287⟩,
⟨128,495475329,495475604⟩]
theorem checked26174 : checkPrefixCuts (2^48) 3434610689 9 Manual.Count131072.C026174.packed 128 cuts26174 = true := by
 decide +kernel
def pointBounds26174 : List (Nat × Nat × Nat) := [(3434716160,103486588770796,103486971117097)]
theorem point_links_checked26174 : (cuts26174.take 1).map (fun c => (3434610689-1+2*2^9*c.k,103486188930732+c.lower,103486571276810+c.upper)) = pointBounds26174 := by
 decide +kernel
def cuts26175 : List PrefixCut := [⟨80,307634268,307634439⟩,
⟨128,488572855,488573128⟩]
theorem checked26175 : checkPrefixCuts (2^48) 3434741761 9 Manual.Count131072.C026175.packed 128 cuts26175 = true := by
 decide +kernel
def pointBounds26175 : List (Nat × Nat × Nat) := [(3434823680,103486992040329,103487374386853)]
theorem point_links_checked26175 : (cuts26175.take 1).map (fun c => (3434741761-1+2*2^9*c.k,103486684406061+c.lower,103487066752414+c.upper)) = pointBounds26175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000192
