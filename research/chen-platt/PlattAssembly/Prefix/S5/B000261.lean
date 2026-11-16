import PlattAssemblyKernel
import PlattCertificates.Count131072.C048352
import PlattCertificates.Count131072.C048353
import PlattCertificates.Count131072.C048354
import PlattCertificates.Count131072.C048355
import PlattCertificates.Count131072.C048356
import PlattCertificates.Count131072.C048357
import PlattCertificates.Count131072.C048358
import PlattCertificates.Count131072.C048359
import PlattCertificates.Count131072.C048360
import PlattCertificates.Count131072.C048361
import PlattCertificates.Count131072.C048362
import PlattCertificates.Count131072.C048363
import PlattCertificates.Count131072.C048364
import PlattCertificates.Count131072.C048365
import PlattCertificates.Count131072.C048366
import PlattCertificates.Count131072.C048367
import PlattCertificates.Count131072.C048368
import PlattCertificates.Count131072.C048369
import PlattCertificates.Count131072.C048370
import PlattCertificates.Count131072.C048371
import PlattCertificates.Count131072.C048372
import PlattCertificates.Count131072.C048373
import PlattCertificates.Count131072.C048374
import PlattCertificates.Count131072.C048375
import PlattCertificates.Count131072.C048376
import PlattCertificates.Count131072.C048377
import PlattCertificates.Count131072.C048378
import PlattCertificates.Count131072.C048379
import PlattCertificates.Count131072.C048380
import PlattCertificates.Count131072.C048381
import PlattCertificates.Count131072.C048382
import PlattCertificates.Count131072.C048383
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000261
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48352 : List PrefixCut := [⟨64,258235029,258235176⟩]
theorem checked48352 : checkPrefixCuts (2^48) 6341525505 10 Manual.Count131072.C048352.packed 64 cuts48352 = true := by
 decide +kernel
def cuts48353 : List PrefixCut := [⟨12,49311722,49311749⟩,
⟨64,257741465,257741608⟩]
theorem checked48353 : checkPrefixCuts (2^48) 6341656577 10 Manual.Count131072.C048353.packed 64 cuts48353 = true := by
 decide +kernel
def pointBounds48353 : List (Nat × Nat × Nat) := [(6341681152,111239786413238,111240173297371)]
theorem point_links_checked48353 : (cuts48353.take 1).map (fun c => (6341656577-1+2*2^10*c.k,111239737101516+c.lower,111240123985622+c.upper)) = pointBounds48353 := by
 decide +kernel
def cuts48354 : List PrefixCut := [⟨45,180065227,180065330⟩,
⟨64,256759704,256759849⟩]
theorem checked48354 : checkPrefixCuts (2^48) 6341787649 10 Manual.Count131072.C048354.packed 64 cuts48354 = true := by
 decide +kernel
def pointBounds48354 : List (Nat × Nat × Nat) := [(6341879808,111240174908208,111240561792560)]
theorem point_links_checked48354 : (cuts48354.take 1).map (fun c => (6341787649-1+2*2^10*c.k,111239994842981+c.lower,111240381727230+c.upper)) = pointBounds48354 := by
 decide +kernel
def cuts48355 : List PrefixCut := [⟨64,258751617,258751764⟩]
theorem checked48355 : checkPrefixCuts (2^48) 6341918721 10 Manual.Count131072.C048355.packed 64 cuts48355 = true := by
 decide +kernel
def cuts48356 : List PrefixCut := [⟨14,56542949,56542978⟩,
⟨64,255151356,255151501⟩]
theorem checked48356 : checkPrefixCuts (2^48) 6342049793 10 Manual.Count131072.C048356.packed 64 cuts48356 = true := by
 decide +kernel
def pointBounds48356 : List (Nat × Nat × Nat) := [(6342078464,111240566897251,111240953781821)]
theorem point_links_checked48356 : (cuts48356.take 1).map (fun c => (6342049793-1+2*2^10*c.k,111240510354302+c.lower,111240897238843+c.upper)) = pointBounds48356 := by
 decide +kernel
def cuts48357 : List PrefixCut := [⟨47,187288101,187288206⟩,
⟨64,256299953,256300094⟩]
theorem checked48357 : checkPrefixCuts (2^48) 6342180865 10 Manual.Count131072.C048357.packed 64 cuts48357 = true := by
 decide +kernel
def pointBounds48357 : List (Nat × Nat × Nat) := [(6342277120,111240952793759,111241339678550)]
theorem point_links_checked48357 : (cuts48357.take 1).map (fun c => (6342180865-1+2*2^10*c.k,111240765505658+c.lower,111241152390344+c.upper)) = pointBounds48357 := by
 decide +kernel
def cuts48358 : List PrefixCut := [⟨64,256738492,256738633⟩]
theorem checked48358 : checkPrefixCuts (2^48) 6342311937 10 Manual.Count131072.C048358.packed 64 cuts48358 = true := by
 decide +kernel
def cuts48359 : List PrefixCut := [⟨16,64217078,64217114⟩,
⟨64,257354471,257354614⟩]
theorem checked48359 : checkPrefixCuts (2^48) 6342443009 10 Manual.Count131072.C048359.packed 64 cuts48359 = true := by
 decide +kernel
def pointBounds48359 : List (Nat × Nat × Nat) := [(6342475776,111241342761181,111241729646185)]
theorem point_links_checked48359 : (cuts48359.take 1).map (fun c => (6342443009-1+2*2^10*c.k,111241278544103+c.lower,111241665429071+c.upper)) = pointBounds48359 := by
 decide +kernel
def cuts48360 : List PrefixCut := [⟨49,195131392,195131499⟩,
⟨64,254065171,254065313⟩]
theorem checked48360 : checkPrefixCuts (2^48) 6342574081 10 Manual.Count131072.C048360.packed 64 cuts48360 = true := by
 decide +kernel
def pointBounds48360 : List (Nat × Nat × Nat) := [(6342674432,111241731029966,111242117915184)]
theorem point_links_checked48360 : (cuts48360.take 1).map (fun c => (6342574081-1+2*2^10*c.k,111241535898574+c.lower,111241922783685+c.upper)) = pointBounds48360 := by
 decide +kernel
def cuts48361 : List PrefixCut := [⟨64,254592446,254592597⟩]
theorem checked48361 : checkPrefixCuts (2^48) 6342705153 10 Manual.Count131072.C048361.packed 64 cuts48361 = true := by
 decide +kernel
def cuts48362 : List PrefixCut := [⟨18,75440371,75440417⟩,
⟨64,261820547,261820700⟩]
theorem checked48362 : checkPrefixCuts (2^48) 6342836225 10 Manual.Count131072.C048362.packed 64 cuts48362 = true := by
 decide +kernel
def pointBounds48362 : List (Nat × Nat × Nat) := [(6342873088,111242119996562,111242506882012)]
theorem point_links_checked48362 : (cuts48362.take 1).map (fun c => (6342836225-1+2*2^10*c.k,111242044556191+c.lower,111242431441595+c.upper)) = pointBounds48362 := by
 decide +kernel
def cuts48363 : List PrefixCut := [⟨51,205591851,205591970⟩,
⟨64,258353817,258353968⟩]
theorem checked48363 : checkPrefixCuts (2^48) 6342967297 10 Manual.Count131072.C048363.packed 64 cuts48363 = true := by
 decide +kernel
def pointBounds48363 : List (Nat × Nat × Nat) := [(6343071744,111242511968589,111242898854265)]
theorem point_links_checked48363 : (cuts48363.take 1).map (fun c => (6342967297-1+2*2^10*c.k,111242306376738+c.lower,111242693262295+c.upper)) = pointBounds48363 := by
 decide +kernel
def cuts48364 : List PrefixCut := [⟨64,262963443,262963597⟩]
theorem checked48364 : checkPrefixCuts (2^48) 6343098369 10 Manual.Count131072.C048364.packed 64 cuts48364 = true := by
 decide +kernel
def cuts48365 : List PrefixCut := [⟨20,79163082,79163127⟩,
⟨64,256790072,256790222⟩]
theorem checked48365 : checkPrefixCuts (2^48) 6343229441 10 Manual.Count131072.C048365.packed 64 cuts48365 = true := by
 decide +kernel
def pointBounds48365 : List (Nat × Nat × Nat) := [(6343270400,111242906857080,111243293742987)]
theorem point_links_checked48365 : (cuts48365.take 1).map (fun c => (6343229441-1+2*2^10*c.k,111242827693998+c.lower,111243214579860+c.upper)) = pointBounds48365 := by
 decide +kernel
def cuts48366 : List PrefixCut := [⟨53,212279327,212279450⟩,
⟨64,255631073,255631222⟩]
theorem checked48366 : checkPrefixCuts (2^48) 6343360513 10 Manual.Count131072.C048366.packed 64 cuts48366 = true := by
 decide +kernel
def pointBounds48366 : List (Nat × Nat × Nat) := [(6343469056,111243296763397,111243683649532)]
theorem point_links_checked48366 : (cuts48366.take 1).map (fun c => (6343360513-1+2*2^10*c.k,111243084484070+c.lower,111243471370082+c.upper)) = pointBounds48366 := by
 decide +kernel
def cuts48367 : List PrefixCut := [⟨64,256424485,256424631⟩]
theorem checked48367 : checkPrefixCuts (2^48) 6343491585 10 Manual.Count131072.C048367.packed 64 cuts48367 = true := by
 decide +kernel
def cuts48368 : List PrefixCut := [⟨22,90428427,90428478⟩,
⟨64,257484104,257484250⟩]
theorem checked48368 : checkPrefixCuts (2^48) 6343622657 10 Manual.Count131072.C048368.packed 64 cuts48368 = true := by
 decide +kernel
def pointBounds48368 : List (Nat × Nat × Nat) := [(6343667712,111243686968055,111244073854413)]
theorem point_links_checked48368 : (cuts48368.take 1).map (fun c => (6343622657-1+2*2^10*c.k,111243596539628+c.lower,111243983425935+c.upper)) = pointBounds48368 := by
 decide +kernel
def cuts48369 : List PrefixCut := [⟨55,224734093,224734219⟩,
⟨64,261205863,261206009⟩]
theorem checked48369 : checkPrefixCuts (2^48) 6343753729 10 Manual.Count131072.C048369.packed 64 cuts48369 = true := by
 decide +kernel
def pointBounds48369 : List (Nat × Nat × Nat) := [(6343866368,111244078757825,111244465644404)]
theorem point_links_checked48369 : (cuts48369.take 1).map (fun c => (6343753729-1+2*2^10*c.k,111243854023732+c.lower,111244240910185+c.upper)) = pointBounds48369 := by
 decide +kernel
def cuts48370 : List PrefixCut := [⟨64,254811333,254811473⟩]
theorem checked48370 : checkPrefixCuts (2^48) 6343884801 10 Manual.Count131072.C048370.packed 64 cuts48370 = true := by
 decide +kernel
def cuts48371 : List PrefixCut := [⟨24,96723105,96723161⟩,
⟨64,257645618,257645773⟩]
theorem checked48371 : checkPrefixCuts (2^48) 6344015873 10 Manual.Count131072.C048371.packed 64 cuts48371 = true := by
 decide +kernel
def pointBounds48371 : List (Nat × Nat × Nat) := [(6344065024,111244466764033,111244853650828)]
theorem point_links_checked48371 : (cuts48371.take 1).map (fun c => (6344015873-1+2*2^10*c.k,111244370040928+c.lower,111244756927667+c.upper)) = pointBounds48371 := by
 decide +kernel
def cuts48372 : List PrefixCut := [⟨57,230221621,230221755⟩,
⟨64,258394528,258394679⟩]
theorem checked48372 : checkPrefixCuts (2^48) 6344146945 10 Manual.Count131072.C048372.packed 64 cuts48372 = true := by
 decide +kernel
def pointBounds48372 : List (Nat × Nat × Nat) := [(6344263680,111244857908167,111245244795195)]
theorem point_links_checked48372 : (cuts48372.take 1).map (fun c => (6344146945-1+2*2^10*c.k,111244627686546+c.lower,111245014573440+c.upper)) = pointBounds48372 := by
 decide +kernel
def cuts48373 : List PrefixCut := [⟨64,253863807,253863950⟩]
theorem checked48373 : checkPrefixCuts (2^48) 6344278017 10 Manual.Count131072.C048373.packed 64 cuts48373 = true := by
 decide +kernel
def cuts48374 : List PrefixCut := [⟨26,106388785,106388847⟩,
⟨64,260735224,260735372⟩]
theorem checked48374 : checkPrefixCuts (2^48) 6344409089 10 Manual.Count131072.C048374.packed 64 cuts48374 = true := by
 decide +kernel
def pointBounds48374 : List (Nat × Nat × Nat) := [(6344462336,111245246333666,111245633220916)]
theorem point_links_checked48374 : (cuts48374.take 1).map (fun c => (6344409089-1+2*2^10*c.k,111245139944881+c.lower,111245526832069+c.upper)) = pointBounds48374 := by
 decide +kernel
def cuts48375 : List PrefixCut := [⟨59,236418309,236418447⟩,
⟨64,256914486,256914637⟩]
theorem checked48375 : checkPrefixCuts (2^48) 6344540161 10 Manual.Count131072.C048375.packed 64 cuts48375 = true := by
 decide +kernel
def pointBounds48375 : List (Nat × Nat × Nat) := [(6344660992,111245637098414,111246023985888)]
theorem point_links_checked48375 : (cuts48375.take 1).map (fun c => (6344540161-1+2*2^10*c.k,111245400680105+c.lower,111245787567441+c.upper)) = pointBounds48375 := by
 decide +kernel
def cuts48376 : List PrefixCut := [⟨64,257663365,257663511⟩]
theorem checked48376 : checkPrefixCuts (2^48) 6344671233 10 Manual.Count131072.C048376.packed 64 cuts48376 = true := by
 decide +kernel
def cuts48377 : List PrefixCut := [⟨28,113746396,113746458⟩,
⟨64,256903890,256904030⟩]
theorem checked48377 : checkPrefixCuts (2^48) 6344802305 10 Manual.Count131072.C048377.packed 64 cuts48377 = true := by
 decide +kernel
def pointBounds48377 : List (Nat × Nat × Nat) := [(6344859648,111246029004352,111246415892047)]
theorem point_links_checked48377 : (cuts48377.take 1).map (fun c => (6344802305-1+2*2^10*c.k,111245915257956+c.lower,111246302145589+c.upper)) = pointBounds48377 := by
 decide +kernel
def cuts48378 : List PrefixCut := [⟨61,245808261,245808405⟩,
⟨64,258185052,258185203⟩]
theorem checked48378 : checkPrefixCuts (2^48) 6344933377 10 Manual.Count131072.C048378.packed 64 cuts48378 = true := by
 decide +kernel
def pointBounds48378 : List (Nat × Nat × Nat) := [(6345058304,111246417970107,111246804858024)]
theorem point_links_checked48378 : (cuts48378.take 1).map (fun c => (6344933377-1+2*2^10*c.k,111246172161846+c.lower,111246559049619+c.upper)) = pointBounds48378 := by
 decide +kernel
def cuts48379 : List PrefixCut := [⟨64,257203782,257203924⟩]
theorem checked48379 : checkPrefixCuts (2^48) 6345064449 10 Manual.Count131072.C048379.packed 64 cuts48379 = true := by
 decide +kernel
def cuts48380 : List PrefixCut := [⟨30,122212086,122212159⟩,
⟨64,259061593,259061746⟩]
theorem checked48380 : checkPrefixCuts (2^48) 6345195521 10 Manual.Count131072.C048380.packed 64 cuts48380 = true := by
 decide +kernel
def pointBounds48380 : List (Nat × Nat × Nat) := [(6345256960,111246809762766,111247196650905)]
theorem point_links_checked48380 : (cuts48380.take 1).map (fun c => (6345195521-1+2*2^10*c.k,111246687550680+c.lower,111247074438746+c.upper)) = pointBounds48380 := by
 decide +kernel
def cuts48381 : List PrefixCut := [⟨63,256039885,256040033⟩,
⟨64,260475734,260475885⟩]
theorem checked48381 : checkPrefixCuts (2^48) 6345326593 10 Manual.Count131072.C048381.packed 64 cuts48381 = true := by
 decide +kernel
def pointBounds48381 : List (Nat × Nat × Nat) := [(6345455616,111247202652158,111247589540525)]
theorem point_links_checked48381 : (cuts48381.take 1).map (fun c => (6345326593-1+2*2^10*c.k,111246946612273+c.lower,111247333500492+c.upper)) = pointBounds48381 := by
 decide +kernel
def cuts48382 : List PrefixCut := [⟨64,254748168,254748312⟩]
theorem checked48382 : checkPrefixCuts (2^48) 6345457665 10 Manual.Count131072.C048382.packed 64 cuts48382 = true := by
 decide +kernel
def cuts48383 : List PrefixCut := [⟨32,130543659,130543726⟩,
⟨64,260464966,260465108⟩]
theorem checked48383 : checkPrefixCuts (2^48) 6345588737 10 Manual.Count131072.C048383.packed 64 cuts48383 = true := by
 decide +kernel
def pointBounds48383 : List (Nat × Nat × Nat) := [(6345654272,111247592379834,111247979268415)]
theorem point_links_checked48383 : (cuts48383.take 1).map (fun c => (6345588737-1+2*2^10*c.k,111247461836175+c.lower,111247848724689+c.upper)) = pointBounds48383 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000261
