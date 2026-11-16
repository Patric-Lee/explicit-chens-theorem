import PlattAssemblyKernel
import PlattCertificates.Count131072.C040128
import PlattCertificates.Count131072.C040129
import PlattCertificates.Count131072.C040130
import PlattCertificates.Count131072.C040131
import PlattCertificates.Count131072.C040132
import PlattCertificates.Count131072.C040133
import PlattCertificates.Count131072.C040134
import PlattCertificates.Count131072.C040135
import PlattCertificates.Count131072.C040136
import PlattCertificates.Count131072.C040137
import PlattCertificates.Count131072.C040138
import PlattCertificates.Count131072.C040139
import PlattCertificates.Count131072.C040140
import PlattCertificates.Count131072.C040141
import PlattCertificates.Count131072.C040142
import PlattCertificates.Count131072.C040143
import PlattCertificates.Count131072.C040144
import PlattCertificates.Count131072.C040145
import PlattCertificates.Count131072.C040146
import PlattCertificates.Count131072.C040147
import PlattCertificates.Count131072.C040148
import PlattCertificates.Count131072.C040149
import PlattCertificates.Count131072.C040150
import PlattCertificates.Count131072.C040151
import PlattCertificates.Count131072.C040152
import PlattCertificates.Count131072.C040153
import PlattCertificates.Count131072.C040154
import PlattCertificates.Count131072.C040155
import PlattCertificates.Count131072.C040156
import PlattCertificates.Count131072.C040157
import PlattCertificates.Count131072.C040158
import PlattCertificates.Count131072.C040159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40128 : List PrefixCut := [⟨16,78021010,78021057⟩,
⟨64,311546376,311546563⟩]
theorem checked40128 : checkPrefixCuts (2^48) 5263589377 10 Manual.Count131072.C040128.packed 64 cuts40128 = true := by
 decide +kernel
def pointBounds40128 : List (Nat × Nat × Nat) := [(5263622144,108906467080161,108906852609637)]
theorem point_links_checked40128 : (cuts40128.take 1).map (fun c => (5263589377-1+2*2^10*c.k,108906389059151+c.lower,108906774588580+c.upper)) = pointBounds40128 := by
 decide +kernel
def cuts40129 : List PrefixCut := [⟨33,162561483,162561581⟩,
⟨64,318169391,318169576⟩]
theorem checked40129 : checkPrefixCuts (2^48) 5263720449 10 Manual.Count131072.C040129.packed 64 cuts40129 = true := by
 decide +kernel
def pointBounds40129 : List (Nat × Nat × Nat) := [(5263788032,108906863167010,108907248696724)]
theorem point_links_checked40129 : (cuts40129.take 1).map (fun c => (5263720449-1+2*2^10*c.k,108906700605527+c.lower,108907086135143+c.upper)) = pointBounds40129 := by
 decide +kernel
def cuts40130 : List PrefixCut := [⟨50,241696428,241696575⟩,
⟨64,309926695,309926882⟩]
theorem checked40130 : checkPrefixCuts (2^48) 5263851521 10 Manual.Count131072.C040130.packed 64 cuts40130 = true := by
 decide +kernel
def pointBounds40130 : List (Nat × Nat × Nat) := [(5263953920,108907260471346,108907646001294)]
theorem point_links_checked40130 : (cuts40130.take 1).map (fun c => (5263851521-1+2*2^10*c.k,108907018774918+c.lower,108907404304719+c.upper)) = pointBounds40130 := by
 decide +kernel
def cuts40131 : List PrefixCut := [⟨64,306069082,306069266⟩]
theorem checked40131 : checkPrefixCuts (2^48) 5263982593 10 Manual.Count131072.C040131.packed 64 cuts40131 = true := by
 decide +kernel
def cuts40132 : List PrefixCut := [⟨3,14490502,14490511⟩,
⟨64,314456224,314456411⟩]
theorem checked40132 : checkPrefixCuts (2^48) 5264113665 10 Manual.Count131072.C040132.packed 64 cuts40132 = true := by
 decide +kernel
def pointBounds40132 : List (Nat × Nat × Nat) := [(5264119808,108907649261197,108908034791378)]
theorem point_links_checked40132 : (cuts40132.take 1).map (fun c => (5264113665-1+2*2^10*c.k,108907634770695+c.lower,108908020300867+c.upper)) = pointBounds40132 := by
 decide +kernel
def cuts40133 : List PrefixCut := [⟨20,95923347,95923405⟩,
⟨64,312149219,312149404⟩]
theorem checked40133 : checkPrefixCuts (2^48) 5264244737 10 Manual.Count131072.C040133.packed 64 cuts40133 = true := by
 decide +kernel
def pointBounds40133 : List (Nat × Nat × Nat) := [(5264285696,108908045150266,108908430680683)]
theorem point_links_checked40133 : (cuts40133.take 1).map (fun c => (5264244737-1+2*2^10*c.k,108907949226919+c.lower,108908334757278+c.upper)) = pointBounds40133 := by
 decide +kernel
def cuts40134 : List PrefixCut := [⟨37,180238860,180238967⟩,
⟨64,311927602,311927789⟩]
theorem checked40134 : checkPrefixCuts (2^48) 5264375809 10 Manual.Count131072.C040134.packed 64 cuts40134 = true := by
 decide +kernel
def pointBounds40134 : List (Nat × Nat × Nat) := [(5264451584,108908441614998,108908827145649)]
theorem point_links_checked40134 : (cuts40134.take 1).map (fun c => (5264375809-1+2*2^10*c.k,108908261376138+c.lower,108908646906682+c.upper)) = pointBounds40134 := by
 decide +kernel
def cuts40135 : List PrefixCut := [⟨54,263373335,263373491⟩,
⟨64,311973291,311973476⟩]
theorem checked40135 : checkPrefixCuts (2^48) 5264506881 10 Manual.Count131072.C040135.packed 64 cuts40135 = true := by
 decide +kernel
def pointBounds40135 : List (Nat × Nat × Nat) := [(5264617472,108908836677075,108909222207962)]
theorem point_links_checked40135 : (cuts40135.take 1).map (fun c => (5264506881-1+2*2^10*c.k,108908573303740+c.lower,108908958834471+c.upper)) = pointBounds40135 := by
 decide +kernel
def cuts40136 : List PrefixCut := [⟨64,312018971,312019155⟩]
theorem checked40136 : checkPrefixCuts (2^48) 5264637953 10 Manual.Count131072.C040136.packed 64 cuts40136 = true := by
 decide +kernel
def cuts40137 : List PrefixCut := [⟨7,31864418,31864439⟩,
⟨64,308536082,308536268⟩]
theorem checked40137 : checkPrefixCuts (2^48) 5264769025 10 Manual.Count131072.C040137.packed 64 cuts40137 = true := by
 decide +kernel
def pointBounds40137 : List (Nat × Nat × Nat) := [(5264783360,108909229160420,108909614691541)]
theorem point_links_checked40137 : (cuts40137.take 1).map (fun c => (5264769025-1+2*2^10*c.k,108909197296002+c.lower,108909582827102+c.upper)) = pointBounds40137 := by
 decide +kernel
def cuts40138 : List PrefixCut := [⟨24,116654704,116654774⟩,
⟨64,314248840,314249028⟩]
theorem checked40138 : checkPrefixCuts (2^48) 5264900097 10 Manual.Count131072.C040138.packed 64 cuts40138 = true := by
 decide +kernel
def pointBounds40138 : List (Nat × Nat × Nat) := [(5264949248,108909622486788,108910008018144)]
theorem point_links_checked40138 : (cuts40138.take 1).map (fun c => (5264900097-1+2*2^10*c.k,108909505832084+c.lower,108909891363370+c.upper)) = pointBounds40138 := by
 decide +kernel
def cuts40139 : List PrefixCut := [⟨41,201974809,201974931⟩,
⟨64,315631007,315631197⟩]
theorem checked40139 : checkPrefixCuts (2^48) 5265031169 10 Manual.Count131072.C040139.packed 64 cuts40139 = true := by
 decide +kernel
def pointBounds40139 : List (Nat × Nat × Nat) := [(5265115136,108910022055733,108910407587329)]
theorem point_links_checked40139 : (cuts40139.take 1).map (fun c => (5265031169-1+2*2^10*c.k,108909820080924+c.lower,108910205612398+c.upper)) = pointBounds40139 := by
 decide +kernel
def cuts40140 : List PrefixCut := [⟨58,286167425,286167596⟩,
⟨64,316852662,316852851⟩]
theorem checked40140 : checkPrefixCuts (2^48) 5265162241 10 Manual.Count131072.C040140.packed 64 cuts40140 = true := by
 decide +kernel
def pointBounds40140 : List (Nat × Nat × Nat) := [(5265281024,108910421879356,108910807411191)]
theorem point_links_checked40140 : (cuts40140.take 1).map (fun c => (5265162241-1+2*2^10*c.k,108910135711931+c.lower,108910521243595+c.upper)) = pointBounds40140 := by
 decide +kernel
def cuts40141 : List PrefixCut := [⟨64,312942345,312942532⟩]
theorem checked40141 : checkPrefixCuts (2^48) 5265293313 10 Manual.Count131072.C040141.packed 64 cuts40141 = true := by
 decide +kernel
def cuts40142 : List PrefixCut := [⟨11,52869063,52869096⟩,
⟨64,313522591,313522776⟩]
theorem checked40142 : checkPrefixCuts (2^48) 5265424385 10 Manual.Count131072.C040142.packed 64 cuts40142 = true := by
 decide +kernel
def pointBounds40142 : List (Nat × Nat × Nat) := [(5265446912,108910818376001,108911203908074)]
theorem point_links_checked40142 : (cuts40142.take 1).map (fun c => (5265424385-1+2*2^10*c.k,108910765506938+c.lower,108911151038978+c.upper)) = pointBounds40142 := by
 decide +kernel
def cuts40143 : List PrefixCut := [⟨28,137968866,137968948⟩,
⟨64,317417037,317417221⟩]
theorem checked40143 : checkPrefixCuts (2^48) 5265555457 10 Manual.Count131072.C040143.packed 64 cuts40143 = true := by
 decide +kernel
def pointBounds40143 : List (Nat × Nat × Nat) := [(5265612800,108911216998395,108911602530702)]
theorem point_links_checked40143 : (cuts40143.take 1).map (fun c => (5265555457-1+2*2^10*c.k,108911079029529+c.lower,108911464561754+c.upper)) = pointBounds40143 := by
 decide +kernel
def cuts40144 : List PrefixCut := [⟨45,217558106,217558238⟩,
⟨64,307680567,307680749⟩]
theorem checked40144 : checkPrefixCuts (2^48) 5265686529 10 Manual.Count131072.C040144.packed 64 cuts40144 = true := by
 decide +kernel
def pointBounds40144 : List (Nat × Nat × Nat) := [(5265778688,108911614004672,108911999537213)]
theorem point_links_checked40144 : (cuts40144.take 1).map (fun c => (5265686529-1+2*2^10*c.k,108911396446566+c.lower,108911781978975+c.upper)) = pointBounds40144 := by
 decide +kernel
def cuts40145 : List PrefixCut := [⟨62,305214196,305214379⟩,
⟨64,314728635,314728824⟩]
theorem checked40145 : checkPrefixCuts (2^48) 5265817601 10 Manual.Count131072.C040145.packed 64 cuts40145 = true := by
 decide +kernel
def pointBounds40145 : List (Nat × Nat × Nat) := [(5265944576,108912009341329,108912394874103)]
theorem point_links_checked40145 : (cuts40145.take 1).map (fun c => (5265817601-1+2*2^10*c.k,108911704127133+c.lower,108912089659724+c.upper)) = pointBounds40145 := by
 decide +kernel
def cuts40146 : List PrefixCut := [⟨64,316965742,316965927⟩]
theorem checked40146 : checkPrefixCuts (2^48) 5265948673 10 Manual.Count131072.C040146.packed 64 cuts40146 = true := by
 decide +kernel
def cuts40147 : List PrefixCut := [⟨15,73601203,73601246⟩,
⟨64,313162915,313163097⟩]
theorem checked40147 : checkPrefixCuts (2^48) 5266079745 10 Manual.Count131072.C040147.packed 64 cuts40147 = true := by
 decide +kernel
def pointBounds40147 : List (Nat × Nat × Nat) := [(5266110464,108912409422713,108912794955721)]
theorem point_links_checked40147 : (cuts40147.take 1).map (fun c => (5266079745-1+2*2^10*c.k,108912335821510+c.lower,108912721354475+c.upper)) = pointBounds40147 := by
 decide +kernel
def cuts40148 : List PrefixCut := [⟨32,154360400,154360495⟩,
⟨64,311177503,311177694⟩]
theorem checked40148 : checkPrefixCuts (2^48) 5266210817 10 Manual.Count131072.C040148.packed 64 cuts40148 = true := by
 decide +kernel
def pointBounds40148 : List (Nat × Nat × Nat) := [(5266276352,108912803344825,108913188878067)]
theorem point_links_checked40148 : (cuts40148.take 1).map (fun c => (5266210817-1+2*2^10*c.k,108912648984425+c.lower,108913034517572+c.upper)) = pointBounds40148 := by
 decide +kernel
def cuts40149 : List PrefixCut := [⟨49,241101155,241101296⟩,
⟨64,312185293,312185475⟩]
theorem checked40149 : checkPrefixCuts (2^48) 5266341889 10 Manual.Count131072.C040149.packed 64 cuts40149 = true := by
 decide +kernel
def pointBounds40149 : List (Nat × Nat × Nat) := [(5266442240,108913201263083,108913586796562)]
theorem point_links_checked40149 : (cuts40149.take 1).map (fun c => (5266341889-1+2*2^10*c.k,108912960161928+c.lower,108913345695266+c.upper)) = pointBounds40149 := by
 decide +kernel
def cuts40150 : List PrefixCut := [⟨64,313086093,313086277⟩]
theorem checked40150 : checkPrefixCuts (2^48) 5266472961 10 Manual.Count131072.C040150.packed 64 cuts40150 = true := by
 decide +kernel
def cuts40151 : List PrefixCut := [⟨2,9513248,9513254⟩,
⟨64,308214842,308215027⟩]
theorem checked40151 : checkPrefixCuts (2^48) 5266604033 10 Manual.Count131072.C040151.packed 64 cuts40151 = true := by
 decide +kernel
def pointBounds40151 : List (Nat × Nat × Nat) := [(5266608128,108913594946562,108913980480272)]
theorem point_links_checked40151 : (cuts40151.take 1).map (fun c => (5266604033-1+2*2^10*c.k,108913585433314+c.lower,108913970967018+c.upper)) = pointBounds40151 := by
 decide +kernel
def cuts40152 : List PrefixCut := [⟨19,93045497,93045555⟩,
⟨64,310986228,310986417⟩]
theorem checked40152 : checkPrefixCuts (2^48) 5266735105 10 Manual.Count131072.C040152.packed 64 cuts40152 = true := by
 decide +kernel
def pointBounds40152 : List (Nat × Nat × Nat) := [(5266774016,108913986693653,108914372227600)]
theorem point_links_checked40152 : (cuts40152.take 1).map (fun c => (5266735105-1+2*2^10*c.k,108913893648156+c.lower,108914279182045+c.upper)) = pointBounds40152 := by
 decide +kernel
def cuts40153 : List PrefixCut := [⟨36,175023224,175023327⟩,
⟨64,313009274,313009459⟩]
theorem checked40153 : checkPrefixCuts (2^48) 5266866177 10 Manual.Count131072.C040153.packed 64 cuts40153 = true := by
 decide +kernel
def pointBounds40153 : List (Nat × Nat × Nat) := [(5266939904,108914379657608,108914765191789)]
theorem point_links_checked40153 : (cuts40153.take 1).map (fun c => (5266866177-1+2*2^10*c.k,108914204634384+c.lower,108914590168462+c.upper)) = pointBounds40153 := by
 decide +kernel
def cuts40154 : List PrefixCut := [⟨53,264584902,264585058⟩,
⟨64,319788453,319788643⟩]
theorem checked40154 : checkPrefixCuts (2^48) 5266997249 10 Manual.Count131072.C040154.packed 64 cuts40154 = true := by
 decide +kernel
def pointBounds40154 : List (Nat × Nat × Nat) := [(5267105792,108914782228560,108915167762979)]
theorem point_links_checked40154 : (cuts40154.take 1).map (fun c => (5266997249-1+2*2^10*c.k,108914517643658+c.lower,108914903177921+c.upper)) = pointBounds40154 := by
 decide +kernel
def cuts40155 : List PrefixCut := [⟨64,310695841,310696027⟩]
theorem checked40155 : checkPrefixCuts (2^48) 5267128321 10 Manual.Count131072.C040155.packed 64 cuts40155 = true := by
 decide +kernel
def cuts40156 : List PrefixCut := [⟨6,29979012,29979031⟩,
⟨64,314321843,314322032⟩]
theorem checked40156 : checkPrefixCuts (2^48) 5267259393 10 Manual.Count131072.C040156.packed 64 cuts40156 = true := by
 decide +kernel
def pointBounds40156 : List (Nat × Nat × Nat) := [(5267271680,108915178106964,108915563641622)]
theorem point_links_checked40156 : (cuts40156.take 1).map (fun c => (5267259393-1+2*2^10*c.k,108915148127952+c.lower,108915533662591+c.upper)) = pointBounds40156 := by
 decide +kernel
def cuts40157 : List PrefixCut := [⟨23,112431483,112431549⟩,
⟨64,316344602,316344790⟩]
theorem checked40157 : checkPrefixCuts (2^48) 5267390465 10 Manual.Count131072.C040157.packed 64 cuts40157 = true := by
 decide +kernel
def pointBounds40157 : List (Nat × Nat × Nat) := [(5267437568,108915574881278,108915960416172)]
theorem point_links_checked40157 : (cuts40157.take 1).map (fun c => (5267390465-1+2*2^10*c.k,108915462449795+c.lower,108915847984623+c.upper)) = pointBounds40157 := by
 decide +kernel
def cuts40158 : List PrefixCut := [⟨40,193062511,193062628⟩,
⟨64,310352001,310352189⟩]
theorem checked40158 : checkPrefixCuts (2^48) 5267521537 10 Manual.Count131072.C040158.packed 64 cuts40158 = true := by
 decide +kernel
def pointBounds40158 : List (Nat × Nat × Nat) := [(5267603456,108915971856908,108916357392041)]
theorem point_links_checked40158 : (cuts40158.take 1).map (fun c => (5267521537-1+2*2^10*c.k,108915778794397+c.lower,108916164329413+c.upper)) = pointBounds40158 := by
 decide +kernel
def cuts40159 : List PrefixCut := [⟨57,280475074,280475240⟩,
⟨64,315473913,315474100⟩]
theorem checked40159 : checkPrefixCuts (2^48) 5267652609 10 Manual.Count131072.C040159.packed 64 cuts40159 = true := by
 decide +kernel
def pointBounds40159 : List (Nat × Nat × Nat) := [(5267769344,108916369621472,108916755156842)]
theorem point_links_checked40159 : (cuts40159.take 1).map (fun c => (5267652609-1+2*2^10*c.k,108916089146398+c.lower,108916474681602+c.upper)) = pointBounds40159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000004
