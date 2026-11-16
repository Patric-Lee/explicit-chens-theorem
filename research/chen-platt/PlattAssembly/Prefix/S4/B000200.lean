import PlattAssemblyKernel
import PlattCertificates.Count131072.C036400
import PlattCertificates.Count131072.C036401
import PlattCertificates.Count131072.C036402
import PlattCertificates.Count131072.C036403
import PlattCertificates.Count131072.C036404
import PlattCertificates.Count131072.C036405
import PlattCertificates.Count131072.C036406
import PlattCertificates.Count131072.C036407
import PlattCertificates.Count131072.C036408
import PlattCertificates.Count131072.C036409
import PlattCertificates.Count131072.C036410
import PlattCertificates.Count131072.C036411
import PlattCertificates.Count131072.C036412
import PlattCertificates.Count131072.C036413
import PlattCertificates.Count131072.C036414
import PlattCertificates.Count131072.C036415
import PlattCertificates.Count131072.C036416
import PlattCertificates.Count131072.C036417
import PlattCertificates.Count131072.C036418
import PlattCertificates.Count131072.C036419
import PlattCertificates.Count131072.C036420
import PlattCertificates.Count131072.C036421
import PlattCertificates.Count131072.C036422
import PlattCertificates.Count131072.C036423
import PlattCertificates.Count131072.C036424
import PlattCertificates.Count131072.C036425
import PlattCertificates.Count131072.C036426
import PlattCertificates.Count131072.C036427
import PlattCertificates.Count131072.C036428
import PlattCertificates.Count131072.C036429
import PlattCertificates.Count131072.C036430
import PlattCertificates.Count131072.C036431
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000200
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36400 : List PrefixCut := [⟨41,220523288,220523427⟩,
⟨64,347494861,347495077⟩]
theorem checked36400 : checkPrefixCuts (2^48) 4774952961 10 Manual.Count131072.C036400.packed 64 cuts36400 = true := by
 decide +kernel
def pointBounds36400 : List (Nat × Nat × Nat) := [(4775036928,107678826000132,107679210789169)]
theorem point_links_checked36400 : (cuts36400.take 1).map (fun c => (4774952961-1+2*2^10*c.k,107678605476844+c.lower,107678990265742+c.upper)) = pointBounds36400 := by
 decide +kernel
def cuts36401 : List PrefixCut := [⟨50,270856646,270856820⟩,
⟨64,346601154,346601374⟩]
theorem checked36401 : checkPrefixCuts (2^48) 4775084033 10 Manual.Count131072.C036401.packed 64 cuts36401 = true := by
 decide +kernel
def pointBounds36401 : List (Nat × Nat × Nat) := [(4775186432,107679223828351,107679608617639)]
theorem point_links_checked36401 : (cuts36401.take 1).map (fun c => (4775084033-1+2*2^10*c.k,107678952971705+c.lower,107679337760819+c.upper)) = pointBounds36401 := by
 decide +kernel
def cuts36402 : List PrefixCut := [⟨59,317002001,317002198⟩,
⟨64,343467592,343467805⟩]
theorem checked36402 : checkPrefixCuts (2^48) 4775215105 10 Manual.Count131072.C036402.packed 64 cuts36402 = true := by
 decide +kernel
def pointBounds36402 : List (Nat × Nat × Nat) := [(4775335936,107679616574860,107680001364391)]
theorem point_links_checked36402 : (cuts36402.take 1).map (fun c => (4775215105-1+2*2^10*c.k,107679299572859+c.lower,107679684362193+c.upper)) = pointBounds36402 := by
 decide +kernel
def cuts36403 : List PrefixCut := [⟨64,346110559,346110776⟩]
theorem checked36403 : checkPrefixCuts (2^48) 4775346177 10 Manual.Count131072.C036403.packed 64 cuts36403 = true := by
 decide +kernel
def cuts36404 : List PrefixCut := [⟨4,21101122,21101135⟩,
⟨64,343802352,343802565⟩]
theorem checked36404 : checkPrefixCuts (2^48) 4775477249 10 Manual.Count131072.C036404.packed 64 cuts36404 = true := by
 decide +kernel
def pointBounds36404 : List (Nat × Nat × Nat) := [(4775485440,107680010252132,107680395041909)]
theorem point_links_checked36404 : (cuts36404.take 1).map (fun c => (4775477249-1+2*2^10*c.k,107679989151010+c.lower,107680373940774+c.upper)) = pointBounds36404 := by
 decide +kernel
def cuts36405 : List PrefixCut := [⟨13,71494152,71494194⟩,
⟨64,347211432,347211646⟩]
theorem checked36405 : checkPrefixCuts (2^48) 4775608321 10 Manual.Count131072.C036405.packed 64 cuts36405 = true := by
 decide +kernel
def pointBounds36405 : List (Nat × Nat × Nat) := [(4775634944,107680404447514,107680789237533)]
theorem point_links_checked36405 : (cuts36405.take 1).map (fun c => (4775608321-1+2*2^10*c.k,107680332953362+c.lower,107680717743339+c.upper)) = pointBounds36405 := by
 decide +kernel
def cuts36406 : List PrefixCut := [⟨22,120823340,120823413⟩,
⟨64,346553612,346553823⟩]
theorem checked36406 : checkPrefixCuts (2^48) 4775739393 10 Manual.Count131072.C036406.packed 64 cuts36406 = true := by
 decide +kernel
def pointBounds36406 : List (Nat × Nat × Nat) := [(4775784448,107680800988134,107681185778398)]
theorem point_links_checked36406 : (cuts36406.take 1).map (fun c => (4775739393-1+2*2^10*c.k,107680680164794+c.lower,107681064954985+c.upper)) = pointBounds36406 := by
 decide +kernel
def cuts36407 : List PrefixCut := [⟨31,168735163,168735264⟩,
⟨64,348430041,348430251⟩]
theorem checked36407 : checkPrefixCuts (2^48) 4775870465 10 Manual.Count131072.C036407.packed 64 cuts36407 = true := by
 decide +kernel
def pointBounds36407 : List (Nat × Nat × Nat) := [(4775933952,107681195453569,107681580244072)]
theorem point_links_checked36407 : (cuts36407.take 1).map (fun c => (4775870465-1+2*2^10*c.k,107681026718406+c.lower,107681411508808+c.upper)) = pointBounds36407 := by
 decide +kernel
def cuts36408 : List PrefixCut := [⟨40,216349484,216349621⟩,
⟨64,346122038,346122256⟩]
theorem checked36408 : checkPrefixCuts (2^48) 4776001537 10 Manual.Count131072.C036408.packed 64 cuts36408 = true := by
 decide +kernel
def pointBounds36408 : List (Nat × Nat × Nat) := [(4776083456,107681591497931,107681976288680)]
theorem point_links_checked36408 : (cuts36408.take 1).map (fun c => (4776001537-1+2*2^10*c.k,107681375148447+c.lower,107681759939059+c.upper)) = pointBounds36408 := by
 decide +kernel
def cuts36409 : List PrefixCut := [⟨49,263784241,263784400⟩,
⟨64,345287493,345287699⟩]
theorem checked36409 : checkPrefixCuts (2^48) 4776132609 10 Manual.Count131072.C036409.packed 64 cuts36409 = true := by
 decide +kernel
def pointBounds36409 : List (Nat × Nat × Nat) := [(4776232960,107681985054726,107682369845715)]
theorem point_links_checked36409 : (cuts36409.take 1).map (fun c => (4776132609-1+2*2^10*c.k,107681721270485+c.lower,107682106061315+c.upper)) = pointBounds36409 := by
 decide +kernel
def cuts36410 : List PrefixCut := [⟨58,313514461,313514656⟩,
⟨64,343981521,343981735⟩]
theorem checked36410 : checkPrefixCuts (2^48) 4776263681 10 Manual.Count131072.C036410.packed 64 cuts36410 = true := by
 decide +kernel
def pointBounds36410 : List (Nat × Nat × Nat) := [(4776382464,107682380072439,107682764863670)]
theorem point_links_checked36410 : (cuts36410.take 1).map (fun c => (4776263681-1+2*2^10*c.k,107682066557978+c.lower,107682451349014+c.upper)) = pointBounds36410 := by
 decide +kernel
def cuts36411 : List PrefixCut := [⟨64,351632899,351633122⟩]
theorem checked36411 : checkPrefixCuts (2^48) 4776394753 10 Manual.Count131072.C036411.packed 64 cuts36411 = true := by
 decide +kernel
def cuts36412 : List PrefixCut := [⟨3,16676838,16676847⟩,
⟨64,344787624,344787831⟩]
theorem checked36412 : checkPrefixCuts (2^48) 4776525825 10 Manual.Count131072.C036412.packed 64 cuts36412 = true := by
 decide +kernel
def pointBounds36412 : List (Nat × Nat × Nat) := [(4776531968,107682778849236,107683163640718)]
theorem point_links_checked36412 : (cuts36412.take 1).map (fun c => (4776525825-1+2*2^10*c.k,107682762172398+c.lower,107683146963871+c.upper)) = pointBounds36412 := by
 decide +kernel
def cuts36413 : List PrefixCut := [⟨12,65939338,65939378⟩,
⟨64,344837115,344837328⟩]
theorem checked36413 : checkPrefixCuts (2^48) 4776656897 10 Manual.Count131072.C036413.packed 64 cuts36413 = true := by
 decide +kernel
def pointBounds36413 : List (Nat × Nat × Nat) := [(4776681472,107683172899360,107683557691080)]
theorem point_links_checked36413 : (cuts36413.take 1).map (fun c => (4776656897-1+2*2^10*c.k,107683106960022+c.lower,107683491751702+c.upper)) = pointBounds36413 := by
 decide +kernel
def cuts36414 : List PrefixCut := [⟨21,113018710,113018781⟩,
⟨64,346418614,346418829⟩]
theorem checked36414 : checkPrefixCuts (2^48) 4776787969 10 Manual.Count131072.C036414.packed 64 cuts36414 = true := by
 decide +kernel
def pointBounds36414 : List (Nat × Nat × Nat) := [(4776830976,107683564815847,107683949607811)]
theorem point_links_checked36414 : (cuts36414.take 1).map (fun c => (4776787969-1+2*2^10*c.k,107683451797137+c.lower,107683836589030+c.upper)) = pointBounds36414 := by
 decide +kernel
def cuts36415 : List PrefixCut := [⟨30,160861290,160861388⟩,
⟨64,343403982,343404192⟩]
theorem checked36415 : checkPrefixCuts (2^48) 4776919041 10 Manual.Count131072.C036415.packed 64 cuts36415 = true := by
 decide +kernel
def pointBounds36415 : List (Nat × Nat × Nat) := [(4776980480,107683959077041,107684343869247)]
theorem point_links_checked36415 : (cuts36415.take 1).map (fun c => (4776919041-1+2*2^10*c.k,107683798215751+c.lower,107684183007859+c.upper)) = pointBounds36415 := by
 decide +kernel
def cuts36416 : List PrefixCut := [⟨39,211765053,211765185⟩,
⟨64,347106641,347106857⟩]
theorem checked36416 : checkPrefixCuts (2^48) 4777050113 10 Manual.Count131072.C036416.packed 64 cuts36416 = true := by
 decide +kernel
def pointBounds36416 : List (Nat × Nat × Nat) := [(4777129984,107684353384786,107684738177236)]
theorem point_links_checked36416 : (cuts36416.take 1).map (fun c => (4777050113-1+2*2^10*c.k,107684141619733+c.lower,107684526412051+c.upper)) = pointBounds36416 := by
 decide +kernel
def cuts36417 : List PrefixCut := [⟨48,257362987,257363145⟩,
⟨64,342147854,342148064⟩]
theorem checked36417 : checkPrefixCuts (2^48) 4777181185 10 Manual.Count131072.C036417.packed 64 cuts36417 = true := by
 decide +kernel
def pointBounds36417 : List (Nat × Nat × Nat) := [(4777279488,107684746089361,107685130882053)]
theorem point_links_checked36417 : (cuts36417.take 1).map (fun c => (4777181185-1+2*2^10*c.k,107684488726374+c.lower,107684873518908+c.upper)) = pointBounds36417 := by
 decide +kernel
def cuts36418 : List PrefixCut := [⟨57,312679753,312679946⟩,
⟨64,350210239,350210454⟩]
theorem checked36418 : checkPrefixCuts (2^48) 4777312257 10 Manual.Count131072.C036418.packed 64 cuts36418 = true := by
 decide +kernel
def pointBounds36418 : List (Nat × Nat × Nat) := [(4777428992,107685143553981,107685528346918)]
theorem point_links_checked36418 : (cuts36418.take 1).map (fun c => (4777312257-1+2*2^10*c.k,107684830874228+c.lower,107685215666972+c.upper)) = pointBounds36418 := by
 decide +kernel
def cuts36419 : List PrefixCut := [⟨64,343071761,343071978⟩]
theorem checked36419 : checkPrefixCuts (2^48) 4777443329 10 Manual.Count131072.C036419.packed 64 cuts36419 = true := by
 decide +kernel
def cuts36420 : List PrefixCut := [⟨2,10840513,10840519⟩,
⟨64,346420521,346420730⟩]
theorem checked36420 : checkPrefixCuts (2^48) 4777574401 10 Manual.Count131072.C036420.packed 64 cuts36420 = true := by
 decide +kernel
def pointBounds36420 : List (Nat × Nat × Nat) := [(4777578496,107685534996741,107685919789923)]
theorem point_links_checked36420 : (cuts36420.take 1).map (fun c => (4777574401-1+2*2^10*c.k,107685524156228+c.lower,107685908949404+c.upper)) = pointBounds36420 := by
 decide +kernel
def cuts36421 : List PrefixCut := [⟨11,59797812,59797848⟩,
⟨64,350063591,350063806⟩]
theorem checked36421 : checkPrefixCuts (2^48) 4777705473 10 Manual.Count131072.C036421.packed 64 cuts36421 = true := by
 decide +kernel
def pointBounds36421 : List (Nat × Nat × Nat) := [(4777728000,107685930374561,107686315167982)]
theorem point_links_checked36421 : (cuts36421.take 1).map (fun c => (4777705473-1+2*2^10*c.k,107685870576749+c.lower,107686255370134+c.upper)) = pointBounds36421 := by
 decide +kernel
def cuts36422 : List PrefixCut := [⟨20,105688788,105688855⟩,
⟨64,342748913,342749122⟩]
theorem checked36422 : checkPrefixCuts (2^48) 4777836545 10 Manual.Count131072.C036422.packed 64 cuts36422 = true := by
 decide +kernel
def pointBounds36422 : List (Nat × Nat × Nat) := [(4777877504,107686326329128,107686711122795)]
theorem point_links_checked36422 : (cuts36422.take 1).map (fun c => (4777836545-1+2*2^10*c.k,107686220640340+c.lower,107686605433940+c.upper)) = pointBounds36422 := by
 decide +kernel
def cuts36423 : List PrefixCut := [⟨29,157939434,157939533⟩,
⟨64,349278574,349278784⟩]
theorem checked36423 : checkPrefixCuts (2^48) 4777967617 10 Manual.Count131072.C036423.packed 64 cuts36423 = true := by
 decide +kernel
def pointBounds36423 : List (Nat × Nat × Nat) := [(4778027008,107686721328687,107687106122595)]
theorem point_links_checked36423 : (cuts36423.take 1).map (fun c => (4777967617-1+2*2^10*c.k,107686563389253+c.lower,107686948183062+c.upper)) = pointBounds36423 := by
 decide +kernel
def cuts36424 : List PrefixCut := [⟨38,208596460,208596584⟩,
⟨64,344379657,344379860⟩]
theorem checked36424 : checkPrefixCuts (2^48) 4778098689 10 Manual.Count131072.C036424.packed 64 cuts36424 = true := by
 decide +kernel
def pointBounds36424 : List (Nat × Nat × Nat) := [(4778176512,107687121264287,107687506058430)]
theorem point_links_checked36424 : (cuts36424.take 1).map (fun c => (4778098689-1+2*2^10*c.k,107686912667827+c.lower,107687297461846+c.upper)) = pointBounds36424 := by
 decide +kernel
def cuts36425 : List PrefixCut := [⟨47,255539350,255539507⟩,
⟨64,347374393,347374608⟩]
theorem checked36425 : checkPrefixCuts (2^48) 4778229761 10 Manual.Count131072.C036425.packed 64 cuts36425 = true := by
 decide +kernel
def pointBounds36425 : List (Nat × Nat × Nat) := [(4778326016,107687512586834,107687897381213)]
theorem point_links_checked36425 : (cuts36425.take 1).map (fun c => (4778229761-1+2*2^10*c.k,107687257047484+c.lower,107687641841706+c.upper)) = pointBounds36425 := by
 decide +kernel
def cuts36426 : List PrefixCut := [⟨56,303775412,303775594⟩,
⟨64,347659372,347659582⟩]
theorem checked36426 : checkPrefixCuts (2^48) 4778360833 10 Manual.Count131072.C036426.packed 64 cuts36426 = true := by
 decide +kernel
def pointBounds36426 : List (Nat × Nat × Nat) := [(4778475520,107687908197289,107688292991908)]
theorem point_links_checked36426 : (cuts36426.take 1).map (fun c => (4778360833-1+2*2^10*c.k,107687604421877+c.lower,107687989216314+c.upper)) = pointBounds36426 := by
 decide +kernel
def cuts36427 : List PrefixCut := [⟨64,345882692,345882904⟩]
theorem checked36427 : checkPrefixCuts (2^48) 4778491905 10 Manual.Count131072.C036427.packed 64 cuts36427 = true := by
 decide +kernel
def cuts36428 : List PrefixCut := [⟨1,5419068,5419072⟩,
⟨64,348818333,348818541⟩]
theorem checked36428 : checkPrefixCuts (2^48) 4778622977 10 Manual.Count131072.C036428.packed 64 cuts36428 = true := by
 decide +kernel
def pointBounds36428 : List (Nat × Nat × Nat) := [(4778625024,107688303383009,107688688177872)]
theorem point_links_checked36428 : (cuts36428.take 1).map (fun c => (4778622977-1+2*2^10*c.k,107688297963941+c.lower,107688682758800+c.upper)) = pointBounds36428 := by
 decide +kernel
def cuts36429 : List PrefixCut := [⟨10,54130192,54130224⟩,
⟨64,343507751,343507960⟩]
theorem checked36429 : checkPrefixCuts (2^48) 4778754049 10 Manual.Count131072.C036429.packed 64 cuts36429 = true := by
 decide +kernel
def pointBounds36429 : List (Nat × Nat × Nat) := [(4778774528,107688700912466,107689085707565)]
theorem point_links_checked36429 : (cuts36429.take 1).map (fun c => (4778754049-1+2*2^10*c.k,107688646782274+c.lower,107689031577341+c.upper)) = pointBounds36429 := by
 decide +kernel
def cuts36430 : List PrefixCut := [⟨19,105842325,105842390⟩,
⟨64,352038687,352038904⟩]
theorem checked36430 : checkPrefixCuts (2^48) 4778885121 10 Manual.Count131072.C036430.packed 64 cuts36430 = true := by
 decide +kernel
def pointBounds36430 : List (Nat × Nat × Nat) := [(4778924032,107689096132350,107689480927691)]
theorem point_links_checked36430 : (cuts36430.take 1).map (fun c => (4778885121-1+2*2^10*c.k,107688990290025+c.lower,107689375085301+c.upper)) = pointBounds36430 := by
 decide +kernel
def cuts36431 : List PrefixCut := [⟨28,148422274,148422366⟩,
⟨64,343842249,343842463⟩]
theorem checked36431 : checkPrefixCuts (2^48) 4779016193 10 Manual.Count131072.C036431.packed 64 cuts36431 = true := by
 decide +kernel
def pointBounds36431 : List (Nat × Nat × Nat) := [(4779073536,107689490750986,107689875546571)]
theorem point_links_checked36431 : (cuts36431.take 1).map (fun c => (4779016193-1+2*2^10*c.k,107689342328712+c.lower,107689727124205+c.upper)) = pointBounds36431 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000200
