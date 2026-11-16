import PlattAssemblyKernel
import PlattCertificates.Count131072.C060256
import PlattCertificates.Count131072.C060257
import PlattCertificates.Count131072.C060258
import PlattCertificates.Count131072.C060259
import PlattCertificates.Count131072.C060260
import PlattCertificates.Count131072.C060261
import PlattCertificates.Count131072.C060262
import PlattCertificates.Count131072.C060263
import PlattCertificates.Count131072.C060264
import PlattCertificates.Count131072.C060265
import PlattCertificates.Count131072.C060266
import PlattCertificates.Count131072.C060267
import PlattCertificates.Count131072.C060268
import PlattCertificates.Count131072.C060269
import PlattCertificates.Count131072.C060270
import PlattCertificates.Count131072.C060271
import PlattCertificates.Count131072.C060272
import PlattCertificates.Count131072.C060273
import PlattCertificates.Count131072.C060274
import PlattCertificates.Count131072.C060275
import PlattCertificates.Count131072.C060276
import PlattCertificates.Count131072.C060277
import PlattCertificates.Count131072.C060278
import PlattCertificates.Count131072.C060279
import PlattCertificates.Count131072.C060280
import PlattCertificates.Count131072.C060281
import PlattCertificates.Count131072.C060282
import PlattCertificates.Count131072.C060283
import PlattCertificates.Count131072.C060284
import PlattCertificates.Count131072.C060285
import PlattCertificates.Count131072.C060286
import PlattCertificates.Count131072.C060287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60256 : List PrefixCut := [⟨6,19378128,19378140⟩,
⟨64,205214260,205214383⟩]
theorem checked60256 : checkPrefixCuts (2^48) 7901806593 10 Manual.Count131072.C060256.packed 64 cuts60256 = true := by
 decide +kernel
def pointBounds60256 : List (Nat × Nat × Nat) := [(7901818880,113969366128351,113969754565613)]
theorem point_links_checked60256 : (cuts60256.take 1).map (fun c => (7901806593-1+2*2^10*c.k,113969346750223+c.lower,113969735187473+c.upper)) = pointBounds60256 := by
 decide +kernel
def cuts60257 : List PrefixCut := [⟨63,201648823,201648937⟩,
⟨64,204498456,204498572⟩]
theorem checked60257 : checkPrefixCuts (2^48) 7901937665 10 Manual.Count131072.C060257.packed 64 cuts60257 = true := by
 decide +kernel
def pointBounds60257 : List (Nat × Nat × Nat) := [(7902066688,113969753613306,113970142050793)]
theorem point_links_checked60257 : (cuts60257.take 1).map (fun c => (7901937665-1+2*2^10*c.k,113969551964483+c.lower,113969940401856+c.upper)) = pointBounds60257 := by
 decide +kernel
def cuts60258 : List PrefixCut := [⟨64,206418559,206418679⟩]
theorem checked60258 : checkPrefixCuts (2^48) 7902068737 10 Manual.Count131072.C060258.packed 64 cuts60258 = true := by
 decide +kernel
def cuts60259 : List PrefixCut := [⟨56,176922335,176922439⟩,
⟨64,201179052,201179169⟩]
theorem checked60259 : checkPrefixCuts (2^48) 7902199809 10 Manual.Count131072.C060259.packed 64 cuts60259 = true := by
 decide +kernel
def pointBounds60259 : List (Nat × Nat × Nat) := [(7902314496,113970139803833,113970528241546)]
theorem point_links_checked60259 : (cuts60259.take 1).map (fun c => (7902199809-1+2*2^10*c.k,113969962881498+c.lower,113970351319107+c.upper)) = pointBounds60259 := by
 decide +kernel
def cuts60260 : List PrefixCut := [⟨64,205022571,205022692⟩]
theorem checked60260 : checkPrefixCuts (2^48) 7902330881 10 Manual.Count131072.C060260.packed 64 cuts60260 = true := by
 decide +kernel
def cuts60261 : List PrefixCut := [⟨49,156792238,156792327⟩,
⟨64,203558818,203558935⟩]
theorem checked60261 : checkPrefixCuts (2^48) 7902461953 10 Manual.Count131072.C060261.packed 64 cuts60261 = true := by
 decide +kernel
def pointBounds60261 : List (Nat × Nat × Nat) := [(7902562304,113970525875359,113970914313295)]
theorem point_links_checked60261 : (cuts60261.take 1).map (fun c => (7902461953-1+2*2^10*c.k,113970369083121+c.lower,113970757520968+c.upper)) = pointBounds60261 := by
 decide +kernel
def cuts60262 : List PrefixCut := [⟨64,208221348,208221461⟩]
theorem checked60262 : checkPrefixCuts (2^48) 7902593025 10 Manual.Count131072.C060262.packed 64 cuts60262 = true := by
 decide +kernel
def cuts60263 : List PrefixCut := [⟨42,134312680,134312757⟩,
⟨64,204478100,204478214⟩]
theorem checked60263 : checkPrefixCuts (2^48) 7902724097 10 Manual.Count131072.C060263.packed 64 cuts60263 = true := by
 decide +kernel
def pointBounds60263 : List (Nat × Nat × Nat) := [(7902810112,113970915175967,113971303614121)]
theorem point_links_checked60263 : (cuts60263.take 1).map (fun c => (7902724097-1+2*2^10*c.k,113970780863287+c.lower,113971169301364+c.upper)) = pointBounds60263 := by
 decide +kernel
def cuts60264 : List PrefixCut := [⟨64,204795265,204795384⟩]
theorem checked60264 : checkPrefixCuts (2^48) 7902855169 10 Manual.Count131072.C060264.packed 64 cuts60264 = true := by
 decide +kernel
def cuts60265 : List PrefixCut := [⟨35,109982550,109982616⟩,
⟨64,202939823,202939943⟩]
theorem checked60265 : checkPrefixCuts (2^48) 7902986241 10 Manual.Count131072.C060265.packed 64 cuts60265 = true := by
 decide +kernel
def pointBounds60265 : List (Nat × Nat × Nat) := [(7903057920,113971300119202,113971688557578)]
theorem point_links_checked60265 : (cuts60265.take 1).map (fun c => (7902986241-1+2*2^10*c.k,113971190136652+c.lower,113971578574962+c.upper)) = pointBounds60265 := by
 decide +kernel
def cuts60266 : List PrefixCut := [⟨64,206676067,206676182⟩]
theorem checked60266 : checkPrefixCuts (2^48) 7903117313 10 Manual.Count131072.C060266.packed 64 cuts60266 = true := by
 decide +kernel
def cuts60267 : List PrefixCut := [⟨28,91886593,91886645⟩,
⟨64,208489003,208489123⟩]
theorem checked60267 : checkPrefixCuts (2^48) 7903248385 10 Manual.Count131072.C060267.packed 64 cuts60267 = true := by
 decide +kernel
def pointBounds60267 : List (Nat × Nat × Nat) := [(7903305728,113971691639135,113972080077732)]
theorem point_links_checked60267 : (cuts60267.take 1).map (fun c => (7903248385-1+2*2^10*c.k,113971599752542+c.lower,113971988191087+c.upper)) = pointBounds60267 := by
 decide +kernel
def cuts60268 : List PrefixCut := [⟨64,206028157,206028277⟩]
theorem checked60268 : checkPrefixCuts (2^48) 7903379457 10 Manual.Count131072.C060268.packed 64 cuts60268 = true := by
 decide +kernel
def cuts60269 : List PrefixCut := [⟨21,67701855,67701892⟩,
⟨64,206274043,206274159⟩]
theorem checked60269 : checkPrefixCuts (2^48) 7903510529 10 Manual.Count131072.C060269.packed 64 cuts60269 = true := by
 decide +kernel
def pointBounds60269 : List (Nat × Nat × Nat) := [(7903553536,113972081971557,113972470410379)]
theorem point_links_checked60269 : (cuts60269.take 1).map (fun c => (7903510529-1+2*2^10*c.k,113972014269702+c.lower,113972402708487+c.upper)) = pointBounds60269 := by
 decide +kernel
def cuts60270 : List PrefixCut := [⟨64,205629585,205629702⟩]
theorem checked60270 : checkPrefixCuts (2^48) 7903641601 10 Manual.Count131072.C060270.packed 64 cuts60270 = true := by
 decide +kernel
def cuts60271 : List PrefixCut := [⟨14,45477370,45477394⟩,
⟨64,205448114,205448230⟩]
theorem checked60271 : checkPrefixCuts (2^48) 7903772673 10 Manual.Count131072.C060271.packed 64 cuts60271 = true := by
 decide +kernel
def pointBounds60271 : List (Nat × Nat × Nat) := [(7903801344,113972471650700,113972860089742)]
theorem point_links_checked60271 : (cuts60271.take 1).map (fun c => (7903772673-1+2*2^10*c.k,113972426173330+c.lower,113972814612348+c.upper)) = pointBounds60271 := by
 decide +kernel
def cuts60272 : List PrefixCut := [⟨64,207403366,207403483⟩]
theorem checked60272 : checkPrefixCuts (2^48) 7903903745 10 Manual.Count131072.C060272.packed 64 cuts60272 = true := by
 decide +kernel
def cuts60273 : List PrefixCut := [⟨7,22862592,22862604⟩,
⟨64,202414358,202414472⟩]
theorem checked60273 : checkPrefixCuts (2^48) 7904034817 10 Manual.Count131072.C060273.packed 64 cuts60273 = true := by
 decide +kernel
def pointBounds60273 : List (Nat × Nat × Nat) := [(7904049152,113972861887402,113973250326665)]
theorem point_links_checked60273 : (cuts60273.take 1).map (fun c => (7904034817-1+2*2^10*c.k,113972839024810+c.lower,113973227464061+c.upper)) = pointBounds60273 := by
 decide +kernel
def cuts60274 : List PrefixCut := [⟨64,204227143,204227256⟩]
theorem checked60274 : checkPrefixCuts (2^48) 7904165889 10 Manual.Count131072.C060274.packed 64 cuts60274 = true := by
 decide +kernel
def pointBounds60274 : List (Nat × Nat × Nat) := [(7904296960,113973245666311,113973634105789)]
theorem point_links_checked60274 : (cuts60274.take 1).map (fun c => (7904165889-1+2*2^10*c.k,113973041439168+c.lower,113973429878533+c.upper)) = pointBounds60274 := by
 decide +kernel
def cuts60275 : List PrefixCut := [⟨64,205398879,205398997⟩]
theorem checked60275 : checkPrefixCuts (2^48) 7904296961 10 Manual.Count131072.C060275.packed 64 cuts60275 = true := by
 decide +kernel
def cuts60276 : List PrefixCut := [⟨57,181537286,181537391⟩,
⟨64,203828655,203828773⟩]
theorem checked60276 : checkPrefixCuts (2^48) 7904428033 10 Manual.Count131072.C060276.packed 64 cuts60276 = true := by
 decide +kernel
def pointBounds60276 : List (Nat × Nat × Nat) := [(7904544768,113973632602476,113974021042177)]
theorem point_links_checked60276 : (cuts60276.take 1).map (fun c => (7904428033-1+2*2^10*c.k,113973451065190+c.lower,113973839504786+c.upper)) = pointBounds60276 := by
 decide +kernel
def cuts60277 : List PrefixCut := [⟨64,204038933,204039053⟩]
theorem checked60277 : checkPrefixCuts (2^48) 7904559105 10 Manual.Count131072.C060277.packed 64 cuts60277 = true := by
 decide +kernel
def cuts60278 : List PrefixCut := [⟨50,161483925,161484015⟩,
⟨64,206421306,206421422⟩]
theorem checked60278 : checkPrefixCuts (2^48) 7904690177 10 Manual.Count131072.C060278.packed 64 cuts60278 = true := by
 decide +kernel
def pointBounds60278 : List (Nat × Nat × Nat) := [(7904792576,113974020416703,113974408856627)]
theorem point_links_checked60278 : (cuts60278.take 1).map (fun c => (7904690177-1+2*2^10*c.k,113973858932778+c.lower,113974247372612+c.upper)) = pointBounds60278 := by
 decide +kernel
def cuts60279 : List PrefixCut := [⟨64,205776947,205777064⟩]
theorem checked60279 : checkPrefixCuts (2^48) 7904821249 10 Manual.Count131072.C060279.packed 64 cuts60279 = true := by
 decide +kernel
def cuts60280 : List PrefixCut := [⟨43,137194600,137194680⟩,
⟨64,204883350,204883470⟩]
theorem checked60280 : checkPrefixCuts (2^48) 7904952321 10 Manual.Count131072.C060280.packed 64 cuts60280 = true := by
 decide +kernel
def pointBounds60280 : List (Nat × Nat × Nat) := [(7905040384,113974408325631,113974796765778)]
theorem point_links_checked60280 : (cuts60280.take 1).map (fun c => (7904952321-1+2*2^10*c.k,113974271131031+c.lower,113974659571098+c.upper)) = pointBounds60280 := by
 decide +kernel
def cuts60281 : List PrefixCut := [⟨64,205022386,205022505⟩]
theorem checked60281 : checkPrefixCuts (2^48) 7905083393 10 Manual.Count131072.C060281.packed 64 cuts60281 = true := by
 decide +kernel
def cuts60282 : List PrefixCut := [⟨36,115790934,115790998⟩,
⟨64,205873533,205873647⟩]
theorem checked60282 : checkPrefixCuts (2^48) 7905214465 10 Manual.Count131072.C060282.packed 64 cuts60282 = true := by
 decide +kernel
def pointBounds60282 : List (Nat × Nat × Nat) := [(7905288192,113974796827701,113975185268071)]
theorem point_links_checked60282 : (cuts60282.take 1).map (fun c => (7905214465-1+2*2^10*c.k,113974681036767+c.lower,113975069477073+c.upper)) = pointBounds60282 := by
 decide +kernel
def cuts60283 : List PrefixCut := [⟨64,203377741,203377860⟩]
theorem checked60283 : checkPrefixCuts (2^48) 7905345537 10 Manual.Count131072.C060283.packed 64 cuts60283 = true := by
 decide +kernel
def cuts60284 : List PrefixCut := [⟨29,91931891,91931944⟩,
⟨64,205937893,205938011⟩]
theorem checked60284 : checkPrefixCuts (2^48) 7905476609 10 Manual.Count131072.C060284.packed 64 cuts60284 = true := by
 decide +kernel
def pointBounds60284 : List (Nat × Nat × Nat) := [(7905536000,113975182219932,113975570660524)]
theorem point_links_checked60284 : (cuts60284.take 1).map (fun c => (7905476609-1+2*2^10*c.k,113975090288041+c.lower,113975478728580+c.upper)) = pointBounds60284 := by
 decide +kernel
def cuts60285 : List PrefixCut := [⟨64,204439118,204439240⟩]
theorem checked60285 : checkPrefixCuts (2^48) 7905607681 10 Manual.Count131072.C060285.packed 64 cuts60285 = true := by
 decide +kernel
def cuts60286 : List PrefixCut := [⟨22,69178123,69178163⟩,
⟨64,204542528,204542646⟩]
theorem checked60286 : checkPrefixCuts (2^48) 7905738753 10 Manual.Count131072.C060286.packed 64 cuts60286 = true := by
 decide +kernel
def pointBounds60286 : List (Nat × Nat × Nat) := [(7905783808,113975569843175,113975958283994)]
theorem point_links_checked60286 : (cuts60286.take 1).map (fun c => (7905738753-1+2*2^10*c.k,113975500665052+c.lower,113975889105831+c.upper)) = pointBounds60286 := by
 decide +kernel
def cuts60287 : List PrefixCut := [⟨64,206675324,206675440⟩]
theorem checked60287 : checkPrefixCuts (2^48) 7905869825 10 Manual.Count131072.C060287.packed 64 cuts60287 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000008
