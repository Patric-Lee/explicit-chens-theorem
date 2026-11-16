import PlattAssemblyKernel
import PlattCertificates.Count131072.C075344
import PlattCertificates.Count131072.C075345
import PlattCertificates.Count131072.C075346
import PlattCertificates.Count131072.C075347
import PlattCertificates.Count131072.C075348
import PlattCertificates.Count131072.C075349
import PlattCertificates.Count131072.C075350
import PlattCertificates.Count131072.C075351
import PlattCertificates.Count131072.C075352
import PlattCertificates.Count131072.C075353
import PlattCertificates.Count131072.C075354
import PlattCertificates.Count131072.C075355
import PlattCertificates.Count131072.C075356
import PlattCertificates.Count131072.C075357
import PlattCertificates.Count131072.C075358
import PlattCertificates.Count131072.C075359
import PlattCertificates.Count131072.C075360
import PlattCertificates.Count131072.C075361
import PlattCertificates.Count131072.C075362
import PlattCertificates.Count131072.C075363
import PlattCertificates.Count131072.C075364
import PlattCertificates.Count131072.C075365
import PlattCertificates.Count131072.C075366
import PlattCertificates.Count131072.C075367
import PlattCertificates.Count131072.C075368
import PlattCertificates.Count131072.C075369
import PlattCertificates.Count131072.C075370
import PlattCertificates.Count131072.C075371
import PlattCertificates.Count131072.C075372
import PlattCertificates.Count131072.C075373
import PlattCertificates.Count131072.C075374
import PlattCertificates.Count131072.C075375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75344 : List PrefixCut := [⟨64,162426285,162426385⟩]
theorem checked75344 : checkPrefixCuts (2^48) 9879420929 10 Manual.Count131072.C075344.packed 64 cuts75344 = true := by
 decide +kernel
def cuts75345 : List PrefixCut := [⟨40,99830829,99830893⟩,
⟨64,159916968,159917066⟩]
theorem checked75345 : checkPrefixCuts (2^48) 9879552001 10 Manual.Count131072.C075345.packed 64 cuts75345 = true := by
 decide +kernel
def pointBounds75345 : List (Nat × Nat × Nat) := [(9879633920,116714941482522,116715331523573)]
theorem point_links_checked75345 : (cuts75345.take 1).map (fun c => (9879552001-1+2*2^10*c.k,116714841651693+c.lower,116715231692680+c.upper)) = pointBounds75345 := by
 decide +kernel
def cuts75346 : List PrefixCut := [⟨64,162906316,162906411⟩]
theorem checked75346 : checkPrefixCuts (2^48) 9879683073 10 Manual.Count131072.C075346.packed 64 cuts75346 = true := by
 decide +kernel
def cuts75347 : List PrefixCut := [⟨63,157605083,157605177⟩,
⟨64,160197630,160197725⟩]
theorem checked75347 : checkPrefixCuts (2^48) 9879814145 10 Manual.Count131072.C075347.packed 64 cuts75347 = true := by
 decide +kernel
def pointBounds75347 : List (Nat × Nat × Nat) := [(9879943168,116715322080060,116715712121334)]
theorem point_links_checked75347 : (cuts75347.take 1).map (fun c => (9879814145-1+2*2^10*c.k,116715164474977+c.lower,116715554516157+c.upper)) = pointBounds75347 := by
 decide +kernel
def cuts75348 : List PrefixCut := [⟨64,161221122,161221225⟩]
theorem checked75348 : checkPrefixCuts (2^48) 9879945217 10 Manual.Count131072.C075348.packed 64 cuts75348 = true := by
 decide +kernel
def cuts75349 : List PrefixCut := [⟨64,161845734,161845835⟩]
theorem checked75349 : checkPrefixCuts (2^48) 9880076289 10 Manual.Count131072.C075349.packed 64 cuts75349 = true := by
 decide +kernel
def cuts75350 : List PrefixCut := [⟨22,56977398,56977432⟩,
⟨64,161701159,161701257⟩]
theorem checked75350 : checkPrefixCuts (2^48) 9880207361 10 Manual.Count131072.C075350.packed 64 cuts75350 = true := by
 decide +kernel
def pointBounds75350 : List (Nat × Nat × Nat) := [(9880252416,116715704716861,116716094758374)]
theorem point_links_checked75350 : (cuts75350.take 1).map (fun c => (9880207361-1+2*2^10*c.k,116715647739463+c.lower,116716037780942+c.upper)) = pointBounds75350 := by
 decide +kernel
def cuts75351 : List PrefixCut := [⟨64,159562397,159562494⟩]
theorem checked75351 : checkPrefixCuts (2^48) 9880338433 10 Manual.Count131072.C075351.packed 64 cuts75351 = true := by
 decide +kernel
def cuts75352 : List PrefixCut := [⟨45,114834629,114834694⟩,
⟨64,163035793,163035890⟩]
theorem checked75352 : checkPrefixCuts (2^48) 9880469505 10 Manual.Count131072.C075352.packed 64 cuts75352 = true := by
 decide +kernel
def pointBounds75352 : List (Nat × Nat × Nat) := [(9880561664,116716083837648,116716473879387)]
theorem point_links_checked75352 : (cuts75352.take 1).map (fun c => (9880469505-1+2*2^10*c.k,116715969003019+c.lower,116716359044693+c.upper)) = pointBounds75352 := by
 decide +kernel
def cuts75353 : List PrefixCut := [⟨64,161267414,161267514⟩]
theorem checked75353 : checkPrefixCuts (2^48) 9880600577 10 Manual.Count131072.C075353.packed 64 cuts75353 = true := by
 decide +kernel
def cuts75354 : List PrefixCut := [⟨64,161179810,161179908⟩]
theorem checked75354 : checkPrefixCuts (2^48) 9880731649 10 Manual.Count131072.C075354.packed 64 cuts75354 = true := by
 decide +kernel
def cuts75355 : List PrefixCut := [⟨4,10027375,10027382⟩,
⟨64,162231661,162231759⟩]
theorem checked75355 : checkPrefixCuts (2^48) 9880862721 10 Manual.Count131072.C075355.packed 64 cuts75355 = true := by
 decide +kernel
def pointBounds75355 : List (Nat × Nat × Nat) := [(9880870912,116716464513411,116716854555387)]
theorem point_links_checked75355 : (cuts75355.take 1).map (fun c => (9880862721-1+2*2^10*c.k,116716454486036+c.lower,116716844528005+c.upper)) = pointBounds75355 := by
 decide +kernel
def cuts75356 : List PrefixCut := [⟨64,160577306,160577408⟩]
theorem checked75356 : checkPrefixCuts (2^48) 9880993793 10 Manual.Count131072.C075356.packed 64 cuts75356 = true := by
 decide +kernel
def cuts75357 : List PrefixCut := [⟨27,68138604,68138648⟩,
⟨64,162626163,162626270⟩]
theorem checked75357 : checkPrefixCuts (2^48) 9881124865 10 Manual.Count131072.C075357.packed 64 cuts75357 = true := by
 decide +kernel
def pointBounds75357 : List (Nat × Nat × Nat) := [(9881180160,116716845433607,116717235475820)]
theorem point_links_checked75357 : (cuts75357.take 1).map (fun c => (9881124865-1+2*2^10*c.k,116716777295003+c.lower,116717167337172+c.upper)) = pointBounds75357 := by
 decide +kernel
def cuts75358 : List PrefixCut := [⟨64,162082784,162082880⟩]
theorem checked75358 : checkPrefixCuts (2^48) 9881255937 10 Manual.Count131072.C075358.packed 64 cuts75358 = true := by
 decide +kernel
def cuts75359 : List PrefixCut := [⟨50,126303451,126303522⟩,
⟨64,162308524,162308615⟩]
theorem checked75359 : checkPrefixCuts (2^48) 9881387009 10 Manual.Count131072.C075359.packed 64 cuts75359 = true := by
 decide +kernel
def pointBounds75359 : List (Nat × Nat × Nat) := [(9881489408,116717228307401,116717618349844)]
theorem point_links_checked75359 : (cuts75359.take 1).map (fun c => (9881387009-1+2*2^10*c.k,116717102003950+c.lower,116717492046322+c.upper)) = pointBounds75359 := by
 decide +kernel
def cuts75360 : List PrefixCut := [⟨64,163160911,163161015⟩]
theorem checked75360 : checkPrefixCuts (2^48) 9881518081 10 Manual.Count131072.C075360.packed 64 cuts75360 = true := by
 decide +kernel
def cuts75361 : List PrefixCut := [⟨64,161819981,161820074⟩]
theorem checked75361 : checkPrefixCuts (2^48) 9881649153 10 Manual.Count131072.C075361.packed 64 cuts75361 = true := by
 decide +kernel
def cuts75362 : List PrefixCut := [⟨9,23157657,23157671⟩,
⟨64,164523815,164523914⟩]
theorem checked75362 : checkPrefixCuts (2^48) 9881780225 10 Manual.Count131072.C075362.packed 64 cuts75362 = true := by
 decide +kernel
def pointBounds75362 : List (Nat × Nat × Nat) := [(9881798656,116717612451023,116718002493697)]
theorem point_links_checked75362 : (cuts75362.take 1).map (fun c => (9881780225-1+2*2^10*c.k,116717589293366+c.lower,116717979336026+c.upper)) = pointBounds75362 := by
 decide +kernel
def cuts75363 : List PrefixCut := [⟨64,162271426,162271522⟩]
theorem checked75363 : checkPrefixCuts (2^48) 9881911297 10 Manual.Count131072.C075363.packed 64 cuts75363 = true := by
 decide +kernel
def cuts75364 : List PrefixCut := [⟨32,81433985,81434036⟩,
⟨64,164149170,164149274⟩]
theorem checked75364 : checkPrefixCuts (2^48) 9882042369 10 Manual.Count131072.C075364.packed 64 cuts75364 = true := by
 decide +kernel
def pointBounds75364 : List (Nat × Nat × Nat) := [(9882107904,116717997522592,116718387565498)]
theorem point_links_checked75364 : (cuts75364.take 1).map (fun c => (9882042369-1+2*2^10*c.k,116717916088607+c.lower,116718306131462+c.upper)) = pointBounds75364 := by
 decide +kernel
def cuts75365 : List PrefixCut := [⟨64,161640502,161640599⟩]
theorem checked75365 : checkPrefixCuts (2^48) 9882173441 10 Manual.Count131072.C075365.packed 64 cuts75365 = true := by
 decide +kernel
def cuts75366 : List PrefixCut := [⟨55,138994867,138994956⟩,
⟨64,161780760,161780863⟩]
theorem checked75366 : checkPrefixCuts (2^48) 9882304513 10 Manual.Count131072.C075366.packed 64 cuts75366 = true := by
 decide +kernel
def pointBounds75366 : List (Nat × Nat × Nat) := [(9882417152,116718380873146,116718770916291)]
theorem point_links_checked75366 : (cuts75366.take 1).map (fun c => (9882304513-1+2*2^10*c.k,116718241878279+c.lower,116718631921335+c.upper)) = pointBounds75366 := by
 decide +kernel
def cuts75367 : List PrefixCut := [⟨64,164085680,164085779⟩]
theorem checked75367 : checkPrefixCuts (2^48) 9882435585 10 Manual.Count131072.C075367.packed 64 cuts75367 = true := by
 decide +kernel
def cuts75368 : List PrefixCut := [⟨64,162773332,162773432⟩]
theorem checked75368 : checkPrefixCuts (2^48) 9882566657 10 Manual.Count131072.C075368.packed 64 cuts75368 = true := by
 decide +kernel
def cuts75369 : List PrefixCut := [⟨14,36684227,36684250⟩,
⟨64,164992730,164992833⟩]
theorem checked75369 : checkPrefixCuts (2^48) 9882697729 10 Manual.Count131072.C075369.packed 64 cuts75369 = true := by
 decide +kernel
def pointBounds75369 : List (Nat × Nat × Nat) := [(9882726400,116718767202278,116719157245659)]
theorem point_links_checked75369 : (cuts75369.take 1).map (fun c => (9882697729-1+2*2^10*c.k,116718730518051+c.lower,116719120561409+c.upper)) = pointBounds75369 := by
 decide +kernel
def cuts75370 : List PrefixCut := [⟨64,165019032,165019131⟩]
theorem checked75370 : checkPrefixCuts (2^48) 9882828801 10 Manual.Count131072.C075370.packed 64 cuts75370 = true := by
 decide +kernel
def cuts75371 : List PrefixCut := [⟨37,92818663,92818723⟩,
⟨64,161599149,161599248⟩]
theorem checked75371 : checkPrefixCuts (2^48) 9882959873 10 Manual.Count131072.C075371.packed 64 cuts75371 = true := by
 decide +kernel
def pointBounds75371 : List (Nat × Nat × Nat) := [(9883035648,116719153348476,116719543392096)]
theorem point_links_checked75371 : (cuts75371.take 1).map (fun c => (9882959873-1+2*2^10*c.k,116719060529813+c.lower,116719450573373+c.upper)) = pointBounds75371 := by
 decide +kernel
def cuts75372 : List PrefixCut := [⟨64,159973638,159973734⟩]
theorem checked75372 : checkPrefixCuts (2^48) 9883090945 10 Manual.Count131072.C075372.packed 64 cuts75372 = true := by
 decide +kernel
def cuts75373 : List PrefixCut := [⟨60,152908570,152908662⟩,
⟨64,163189745,163189842⟩]
theorem checked75373 : checkPrefixCuts (2^48) 9883222017 10 Manual.Count131072.C075373.packed 64 cuts75373 = true := by
 decide +kernel
def pointBounds75373 : List (Nat × Nat × Nat) := [(9883344896,116719535011170,116719925055017)]
theorem point_links_checked75373 : (cuts75373.take 1).map (fun c => (9883222017-1+2*2^10*c.k,116719382102600+c.lower,116719772146355+c.upper)) = pointBounds75373 := by
 decide +kernel
def cuts75374 : List PrefixCut := [⟨64,159969399,159969495⟩]
theorem checked75374 : checkPrefixCuts (2^48) 9883353089 10 Manual.Count131072.C075374.packed 64 cuts75374 = true := by
 decide +kernel
def cuts75375 : List PrefixCut := [⟨64,163299334,163299433⟩]
theorem checked75375 : checkPrefixCuts (2^48) 9883484161 10 Manual.Count131072.C075375.packed 64 cuts75375 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000167
