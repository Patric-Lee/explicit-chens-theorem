import PlattAssemblyKernel
import PlattCertificates.Count131072.C046176
import PlattCertificates.Count131072.C046177
import PlattCertificates.Count131072.C046178
import PlattCertificates.Count131072.C046179
import PlattCertificates.Count131072.C046180
import PlattCertificates.Count131072.C046181
import PlattCertificates.Count131072.C046182
import PlattCertificates.Count131072.C046183
import PlattCertificates.Count131072.C046184
import PlattCertificates.Count131072.C046185
import PlattCertificates.Count131072.C046186
import PlattCertificates.Count131072.C046187
import PlattCertificates.Count131072.C046188
import PlattCertificates.Count131072.C046189
import PlattCertificates.Count131072.C046190
import PlattCertificates.Count131072.C046191
import PlattCertificates.Count131072.C046192
import PlattCertificates.Count131072.C046193
import PlattCertificates.Count131072.C046194
import PlattCertificates.Count131072.C046195
import PlattCertificates.Count131072.C046196
import PlattCertificates.Count131072.C046197
import PlattCertificates.Count131072.C046198
import PlattCertificates.Count131072.C046199
import PlattCertificates.Count131072.C046200
import PlattCertificates.Count131072.C046201
import PlattCertificates.Count131072.C046202
import PlattCertificates.Count131072.C046203
import PlattCertificates.Count131072.C046204
import PlattCertificates.Count131072.C046205
import PlattCertificates.Count131072.C046206
import PlattCertificates.Count131072.C046207
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000193
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46176 : List PrefixCut := [⟨64,270860838,270860996⟩]
theorem checked46176 : checkPrefixCuts (2^48) 6056312833 10 Manual.Count131072.C046176.packed 64 cuts46176 = true := by
 decide +kernel
def cuts46177 : List PrefixCut := [⟨8,33090351,33090370⟩,
⟨64,271737976,271738131⟩]
theorem checked46177 : checkPrefixCuts (2^48) 6056443905 10 Manual.Count131072.C046177.packed 64 cuts46177 = true := by
 decide +kernel
def pointBounds46177 : List (Nat × Nat × Nat) := [(6056460288,110665224966383,110665611521429)]
theorem point_links_checked46177 : (cuts46177.take 1).map (fun c => (6056443905-1+2*2^10*c.k,110665191876032+c.lower,110665578431059+c.upper)) = pointBounds46177 := by
 decide +kernel
def cuts46178 : List PrefixCut := [⟨37,155408982,155409074⟩,
⟨64,268107160,268107320⟩]
theorem checked46178 : checkPrefixCuts (2^48) 6056574977 10 Manual.Count131072.C046178.packed 64 cuts46178 = true := by
 decide +kernel
def pointBounds46178 : List (Nat × Nat × Nat) := [(6056650752,110665619022990,110666005578264)]
theorem point_links_checked46178 : (cuts46178.take 1).map (fun c => (6056574977-1+2*2^10*c.k,110665463614008+c.lower,110665850169190+c.upper)) = pointBounds46178 := by
 decide +kernel
def cuts46179 : List PrefixCut := [⟨64,268937871,268938028⟩]
theorem checked46179 : checkPrefixCuts (2^48) 6056706049 10 Manual.Count131072.C046179.packed 64 cuts46179 = true := by
 decide +kernel
def cuts46180 : List PrefixCut := [⟨2,8365004,8365008⟩,
⟨64,271023261,271023417⟩]
theorem checked46180 : checkPrefixCuts (2^48) 6056837121 10 Manual.Count131072.C046180.packed 64 cuts46180 = true := by
 decide +kernel
def pointBounds46180 : List (Nat × Nat × Nat) := [(6056841216,110666009024043,110666395579546)]
theorem point_links_checked46180 : (cuts46180.take 1).map (fun c => (6056837121-1+2*2^10*c.k,110666000659039+c.lower,110666387214538+c.upper)) = pointBounds46180 := by
 decide +kernel
def cuts46181 : List PrefixCut := [⟨31,128910580,128910652⟩,
⟨64,271714448,271714601⟩]
theorem checked46181 : checkPrefixCuts (2^48) 6056968193 10 Manual.Count131072.C046181.packed 64 cuts46181 = true := by
 decide +kernel
def pointBounds46181 : List (Nat × Nat × Nat) := [(6057031680,110666400592880,110666787148607)]
theorem point_links_checked46181 : (cuts46181.take 1).map (fun c => (6056968193-1+2*2^10*c.k,110666271682300+c.lower,110666658237955+c.upper)) = pointBounds46181 := by
 decide +kernel
def cuts46182 : List PrefixCut := [⟨60,251355014,251355155⟩,
⟨64,268827461,268827611⟩]
theorem checked46182 : checkPrefixCuts (2^48) 6057099265 10 Manual.Count131072.C046182.packed 64 cuts46182 = true := by
 decide +kernel
def pointBounds46182 : List (Nat × Nat × Nat) := [(6057222144,110666794751762,110667181307711)]
theorem point_links_checked46182 : (cuts46182.take 1).map (fun c => (6057099265-1+2*2^10*c.k,110666543396748+c.lower,110666929952556+c.upper)) = pointBounds46182 := by
 decide +kernel
def cuts46183 : List PrefixCut := [⟨64,273840274,273840431⟩]
theorem checked46183 : checkPrefixCuts (2^48) 6057230337 10 Manual.Count131072.C046183.packed 64 cuts46183 = true := by
 decide +kernel
def cuts46184 : List PrefixCut := [⟨25,108131129,108131190⟩,
⟨64,273509080,273509242⟩]
theorem checked46184 : checkPrefixCuts (2^48) 6057361409 10 Manual.Count131072.C046184.packed 64 cuts46184 = true := by
 decide +kernel
def pointBounds46184 : List (Nat × Nat × Nat) := [(6057412608,110667194195612,110667580751788)]
theorem point_links_checked46184 : (cuts46184.take 1).map (fun c => (6057361409-1+2*2^10*c.k,110667086064483+c.lower,110667472620598+c.upper)) = pointBounds46184 := by
 decide +kernel
def cuts46185 : List PrefixCut := [⟨54,228012618,228012747⟩,
⟨64,271086881,271087035⟩]
theorem checked46185 : checkPrefixCuts (2^48) 6057492481 10 Manual.Count131072.C046185.packed 64 cuts46185 = true := by
 decide +kernel
def pointBounds46185 : List (Nat × Nat × Nat) := [(6057603072,110667587586181,110667974142587)]
theorem point_links_checked46185 : (cuts46185.take 1).map (fun c => (6057492481-1+2*2^10*c.k,110667359573563+c.lower,110667746129840+c.upper)) = pointBounds46185 := by
 decide +kernel
def cuts46186 : List PrefixCut := [⟨64,270012314,270012466⟩]
theorem checked46186 : checkPrefixCuts (2^48) 6057623553 10 Manual.Count131072.C046186.packed 64 cuts46186 = true := by
 decide +kernel
def cuts46187 : List PrefixCut := [⟨19,77132017,77132064⟩,
⟨64,269355940,269356098⟩]
theorem checked46187 : checkPrefixCuts (2^48) 6057754625 10 Manual.Count131072.C046187.packed 64 cuts46187 = true := by
 decide +kernel
def pointBounds46187 : List (Nat × Nat × Nat) := [(6057793536,110667977804775,110668364361405)]
theorem point_links_checked46187 : (cuts46187.take 1).map (fun c => (6057754625-1+2*2^10*c.k,110667900672758+c.lower,110668287229341+c.upper)) = pointBounds46187 := by
 decide +kernel
def cuts46188 : List PrefixCut := [⟨48,204719680,204719794⟩,
⟨64,273299557,273299712⟩]
theorem checked46188 : checkPrefixCuts (2^48) 6057885697 10 Manual.Count131072.C046188.packed 64 cuts46188 = true := by
 decide +kernel
def pointBounds46188 : List (Nat × Nat × Nat) := [(6057984000,110668374748378,110668761305233)]
theorem point_links_checked46188 : (cuts46188.take 1).map (fun c => (6057885697-1+2*2^10*c.k,110668170028698+c.lower,110668556585439+c.upper)) = pointBounds46188 := by
 decide +kernel
def cuts46189 : List PrefixCut := [⟨64,268926143,268926303⟩]
theorem checked46189 : checkPrefixCuts (2^48) 6058016769 10 Manual.Count131072.C046189.packed 64 cuts46189 = true := by
 decide +kernel
def cuts46190 : List PrefixCut := [⟨13,56683763,56683797⟩,
⟨64,275239125,275239281⟩]
theorem checked46190 : checkPrefixCuts (2^48) 6058147841 10 Manual.Count131072.C046190.packed 64 cuts46190 = true := by
 decide +kernel
def pointBounds46190 : List (Nat × Nat × Nat) := [(6058174464,110668768938161,110669155495251)]
theorem point_links_checked46190 : (cuts46190.take 1).map (fun c => (6058147841-1+2*2^10*c.k,110668712254398+c.lower,110669098811454+c.upper)) = pointBounds46190 := by
 decide +kernel
def cuts46191 : List PrefixCut := [⟨42,179338962,179339063⟩,
⟨64,270168970,270169128⟩]
theorem checked46191 : checkPrefixCuts (2^48) 6058278913 10 Manual.Count131072.C046191.packed 64 cuts46191 = true := by
 decide +kernel
def pointBounds46191 : List (Nat × Nat × Nat) := [(6058364928,110669166832485,110669553389798)]
theorem point_links_checked46191 : (cuts46191.take 1).map (fun c => (6058278913-1+2*2^10*c.k,110668987493523+c.lower,110669374050735+c.upper)) = pointBounds46191 := by
 decide +kernel
def cuts46192 : List PrefixCut := [⟨64,270256007,270256163⟩]
theorem checked46192 : checkPrefixCuts (2^48) 6058409985 10 Manual.Count131072.C046192.packed 64 cuts46192 = true := by
 decide +kernel
def cuts46193 : List PrefixCut := [⟨7,28990498,28990515⟩,
⟨64,271551005,271551158⟩]
theorem checked46193 : checkPrefixCuts (2^48) 6058541057 10 Manual.Count131072.C046193.packed 64 cuts46193 = true := by
 decide +kernel
def pointBounds46193 : List (Nat × Nat × Nat) := [(6058555392,110669556908998,110669943466541)]
theorem point_links_checked46193 : (cuts46193.take 1).map (fun c => (6058541057-1+2*2^10*c.k,110669527918500+c.lower,110669914476026+c.upper)) = pointBounds46193 := by
 decide +kernel
def cuts46194 : List PrefixCut := [⟨36,152056710,152056793⟩,
⟨64,271777415,271777571⟩]
theorem checked46194 : checkPrefixCuts (2^48) 6058672129 10 Manual.Count131072.C046194.packed 64 cuts46194 = true := by
 decide +kernel
def pointBounds46194 : List (Nat × Nat × Nat) := [(6058745856,110669951526215,110670338083977)]
theorem point_links_checked46194 : (cuts46194.take 1).map (fun c => (6058672129-1+2*2^10*c.k,110669799469505+c.lower,110670186027184+c.upper)) = pointBounds46194 := by
 decide +kernel
def cuts46195 : List PrefixCut := [⟨64,271725087,271725245⟩]
theorem checked46195 : checkPrefixCuts (2^48) 6058803201 10 Manual.Count131072.C046195.packed 64 cuts46195 = true := by
 decide +kernel
def cuts46196 : List PrefixCut := [⟨1,4506248,4506251⟩,
⟨64,271161744,271161900⟩]
theorem checked46196 : checkPrefixCuts (2^48) 6058934273 10 Manual.Count131072.C046196.packed 64 cuts46196 = true := by
 decide +kernel
def pointBounds46196 : List (Nat × Nat × Nat) := [(6058936320,110670347478255,110670734036251)]
theorem point_links_checked46196 : (cuts46196.take 1).map (fun c => (6058934273-1+2*2^10*c.k,110670342972007+c.lower,110670729530000+c.upper)) = pointBounds46196 := by
 decide +kernel
def cuts46197 : List PrefixCut := [⟨30,127751063,127751138⟩,
⟨64,270412625,270412781⟩]
theorem checked46197 : checkPrefixCuts (2^48) 6059065345 10 Manual.Count131072.C046197.packed 64 cuts46197 = true := by
 decide +kernel
def pointBounds46197 : List (Nat × Nat × Nat) := [(6059126784,110670741884814,110671128443038)]
theorem point_links_checked46197 : (cuts46197.take 1).map (fun c => (6059065345-1+2*2^10*c.k,110670614133751+c.lower,110671000691900+c.upper)) = pointBounds46197 := by
 decide +kernel
def cuts46198 : List PrefixCut := [⟨59,249502828,249502973⟩,
⟨64,269338343,269338500⟩]
theorem checked46198 : checkPrefixCuts (2^48) 6059196417 10 Manual.Count131072.C046198.packed 64 cuts46198 = true := by
 decide +kernel
def pointBounds46198 : List (Nat × Nat × Nat) := [(6059317248,110671134049204,110671520607654)]
theorem point_links_checked46198 : (cuts46198.take 1).map (fun c => (6059196417-1+2*2^10*c.k,110670884546376+c.lower,110671271104681+c.upper)) = pointBounds46198 := by
 decide +kernel
def cuts46199 : List PrefixCut := [⟨64,271329950,271330108⟩]
theorem checked46199 : checkPrefixCuts (2^48) 6059327489 10 Manual.Count131072.C046199.packed 64 cuts46199 = true := by
 decide +kernel
def cuts46200 : List PrefixCut := [⟨24,103309169,103309226⟩,
⟨64,270023455,270023610⟩]
theorem checked46200 : checkPrefixCuts (2^48) 6059458561 10 Manual.Count131072.C046200.packed 64 cuts46200 = true := by
 decide +kernel
def pointBounds46200 : List (Nat × Nat × Nat) := [(6059507712,110671528523838,110671915082515)]
theorem point_links_checked46200 : (cuts46200.take 1).map (fun c => (6059458561-1+2*2^10*c.k,110671425214669+c.lower,110671811773289+c.upper)) = pointBounds46200 := by
 decide +kernel
def cuts46201 : List PrefixCut := [⟨53,225239600,225239732⟩,
⟨64,270621475,270621636⟩]
theorem checked46201 : checkPrefixCuts (2^48) 6059589633 10 Manual.Count131072.C046201.packed 64 cuts46201 = true := by
 decide +kernel
def pointBounds46201 : List (Nat × Nat × Nat) := [(6059698176,110671920477724,110672307036631)]
theorem point_links_checked46201 : (cuts46201.take 1).map (fun c => (6059589633-1+2*2^10*c.k,110671695238124+c.lower,110672081796899+c.upper)) = pointBounds46201 := by
 decide +kernel
def cuts46202 : List PrefixCut := [⟨64,269315035,269315194⟩]
theorem checked46202 : checkPrefixCuts (2^48) 6059720705 10 Manual.Count131072.C046202.packed 64 cuts46202 = true := by
 decide +kernel
def cuts46203 : List PrefixCut := [⟨18,76919534,76919580⟩,
⟨64,272421240,272421391⟩]
theorem checked46203 : checkPrefixCuts (2^48) 6059851777 10 Manual.Count131072.C046203.packed 64 cuts46203 = true := by
 decide +kernel
def pointBounds46203 : List (Nat × Nat × Nat) := [(6059888640,110672312094168,110672698653309)]
theorem point_links_checked46203 : (cuts46203.take 1).map (fun c => (6059851777-1+2*2^10*c.k,110672235174634+c.lower,110672621733729+c.upper)) = pointBounds46203 := by
 decide +kernel
def cuts46204 : List PrefixCut := [⟨47,195916669,195916782⟩,
⟨64,267538352,267538504⟩]
theorem checked46204 : checkPrefixCuts (2^48) 6059982849 10 Manual.Count131072.C046204.packed 64 cuts46204 = true := by
 decide +kernel
def pointBounds46204 : List (Nat × Nat × Nat) := [(6060079104,110672703512543,110673090071902)]
theorem point_links_checked46204 : (cuts46204.take 1).map (fun c => (6059982849-1+2*2^10*c.k,110672507595874+c.lower,110672894155120+c.upper)) = pointBounds46204 := by
 decide +kernel
def cuts46205 : List PrefixCut := [⟨64,269297524,269297674⟩]
theorem checked46205 : checkPrefixCuts (2^48) 6060113921 10 Manual.Count131072.C046205.packed 64 cuts46205 = true := by
 decide +kernel
def cuts46206 : List PrefixCut := [⟨12,50997743,50997770⟩,
⟨64,271149547,271149696⟩]
theorem checked46206 : checkPrefixCuts (2^48) 6060244993 10 Manual.Count131072.C046206.packed 64 cuts46206 = true := by
 decide +kernel
def pointBounds46206 : List (Nat × Nat × Nat) := [(6060269568,110673095429493,110673481989068)]
theorem point_links_checked46206 : (cuts46206.take 1).map (fun c => (6060244993-1+2*2^10*c.k,110673044431750+c.lower,110673430991298+c.upper)) = pointBounds46206 := by
 decide +kernel
def cuts46207 : List PrefixCut := [⟨41,173424879,173424979⟩,
⟨64,272908563,272908718⟩]
theorem checked46207 : checkPrefixCuts (2^48) 6060376065 10 Manual.Count131072.C046207.packed 64 cuts46207 = true := by
 decide +kernel
def pointBounds46207 : List (Nat × Nat × Nat) := [(6060460032,110673489006176,110673875565973)]
theorem point_links_checked46207 : (cuts46207.take 1).map (fun c => (6060376065-1+2*2^10*c.k,110673315581297+c.lower,110673702140994+c.upper)) = pointBounds46207 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000193
