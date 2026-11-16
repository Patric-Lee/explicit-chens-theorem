import PlattAssemblyKernel
import PlattCertificates.Count131072.C061376
import PlattCertificates.Count131072.C061377
import PlattCertificates.Count131072.C061378
import PlattCertificates.Count131072.C061379
import PlattCertificates.Count131072.C061380
import PlattCertificates.Count131072.C061381
import PlattCertificates.Count131072.C061382
import PlattCertificates.Count131072.C061383
import PlattCertificates.Count131072.C061384
import PlattCertificates.Count131072.C061385
import PlattCertificates.Count131072.C061386
import PlattCertificates.Count131072.C061387
import PlattCertificates.Count131072.C061388
import PlattCertificates.Count131072.C061389
import PlattCertificates.Count131072.C061390
import PlattCertificates.Count131072.C061391
import PlattCertificates.Count131072.C061392
import PlattCertificates.Count131072.C061393
import PlattCertificates.Count131072.C061394
import PlattCertificates.Count131072.C061395
import PlattCertificates.Count131072.C061396
import PlattCertificates.Count131072.C061397
import PlattCertificates.Count131072.C061398
import PlattCertificates.Count131072.C061399
import PlattCertificates.Count131072.C061400
import PlattCertificates.Count131072.C061401
import PlattCertificates.Count131072.C061402
import PlattCertificates.Count131072.C061403
import PlattCertificates.Count131072.C061404
import PlattCertificates.Count131072.C061405
import PlattCertificates.Count131072.C061406
import PlattCertificates.Count131072.C061407
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61376 : List PrefixCut := [⟨37,117644838,117644906⟩,
⟨64,202485518,202485636⟩]
theorem checked61376 : checkPrefixCuts (2^48) 8048607233 10 Manual.Count131072.C061376.packed 64 cuts61376 = true := by
 decide +kernel
def pointBounds61376 : List (Nat × Nat × Nat) := [(8048683008,114196758301975,114197146869309)]
theorem point_links_checked61376 : (cuts61376.take 1).map (fun c => (8048607233-1+2*2^10*c.k,114196640657137+c.lower,114197029224403+c.upper)) = pointBounds61376 := by
 decide +kernel
def cuts61377 : List PrefixCut := [⟨64,200908521,200908638⟩]
theorem checked61377 : checkPrefixCuts (2^48) 8048738305 10 Manual.Count131072.C061377.packed 64 cuts61377 = true := by
 decide +kernel
def cuts61378 : List PrefixCut := [⟨32,99980931,99980989⟩,
⟨64,200310747,200310866⟩]
theorem checked61378 : checkPrefixCuts (2^48) 8048869377 10 Manual.Count131072.C061378.packed 64 cuts61378 = true := by
 decide +kernel
def pointBounds61378 : List (Nat × Nat × Nat) := [(8048934912,114197144032107,114197532599666)]
theorem point_links_checked61378 : (cuts61378.take 1).map (fun c => (8048869377-1+2*2^10*c.k,114197044051176+c.lower,114197432618677+c.upper)) = pointBounds61378 := by
 decide +kernel
def cuts61379 : List PrefixCut := [⟨64,203209987,203210101⟩]
theorem checked61379 : checkPrefixCuts (2^48) 8049000449 10 Manual.Count131072.C061379.packed 64 cuts61379 = true := by
 decide +kernel
def cuts61380 : List PrefixCut := [⟨27,85045772,85045821⟩,
⟨64,202087665,202087784⟩]
theorem checked61380 : checkPrefixCuts (2^48) 8049131521 10 Manual.Count131072.C061380.packed 64 cuts61380 = true := by
 decide +kernel
def pointBounds61380 : List (Nat × Nat × Nat) := [(8049186816,114197532617682,114197921185465)]
theorem point_links_checked61380 : (cuts61380.take 1).map (fun c => (8049131521-1+2*2^10*c.k,114197447571910+c.lower,114197836139644+c.upper)) = pointBounds61380 := by
 decide +kernel
def cuts61381 : List PrefixCut := [⟨64,200440840,200440955⟩]
theorem checked61381 : checkPrefixCuts (2^48) 8049262593 10 Manual.Count131072.C061381.packed 64 cuts61381 = true := by
 decide +kernel
def cuts61382 : List PrefixCut := [⟨22,69726915,69726955⟩,
⟨64,198059758,198059877⟩]
theorem checked61382 : checkPrefixCuts (2^48) 8049393665 10 Manual.Count131072.C061382.packed 64 cuts61382 = true := by
 decide +kernel
def pointBounds61382 : List (Nat × Nat × Nat) := [(8049438720,114197919827330,114198308395338)]
theorem point_links_checked61382 : (cuts61382.take 1).map (fun c => (8049393665-1+2*2^10*c.k,114197850100415+c.lower,114198238668383+c.upper)) = pointBounds61382 := by
 decide +kernel
def cuts61383 : List PrefixCut := [⟨64,201238562,201238675⟩]
theorem checked61383 : checkPrefixCuts (2^48) 8049524737 10 Manual.Count131072.C061383.packed 64 cuts61383 = true := by
 decide +kernel
def cuts61384 : List PrefixCut := [⟨17,52800537,52800570⟩,
⟨64,199626791,199626912⟩]
theorem checked61384 : checkPrefixCuts (2^48) 8049655809 10 Manual.Count131072.C061384.packed 64 cuts61384 = true := by
 decide +kernel
def pointBounds61384 : List (Nat × Nat × Nat) := [(8049690624,114198302199272,114198690767505)]
theorem point_links_checked61384 : (cuts61384.take 1).map (fun c => (8049655809-1+2*2^10*c.k,114198249398735+c.lower,114198637966935+c.upper)) = pointBounds61384 := by
 decide +kernel
def cuts61385 : List PrefixCut := [⟨64,201301950,201302060⟩]
theorem checked61385 : checkPrefixCuts (2^48) 8049786881 10 Manual.Count131072.C061385.packed 64 cuts61385 = true := by
 decide +kernel
def cuts61386 : List PrefixCut := [⟨12,36714437,36714459⟩,
⟨64,201893081,201893195⟩]
theorem checked61386 : checkPrefixCuts (2^48) 8049917953 10 Manual.Count131072.C061386.packed 64 cuts61386 = true := by
 decide +kernel
def pointBounds61386 : List (Nat × Nat × Nat) := [(8049942528,114198687041913,114199075610366)]
theorem point_links_checked61386 : (cuts61386.take 1).map (fun c => (8049917953-1+2*2^10*c.k,114198650327476+c.lower,114199038895907+c.upper)) = pointBounds61386 := by
 decide +kernel
def cuts61387 : List PrefixCut := [⟨64,197728934,197729044⟩]
theorem checked61387 : checkPrefixCuts (2^48) 8050049025 10 Manual.Count131072.C061387.packed 64 cuts61387 = true := by
 decide +kernel
def cuts61388 : List PrefixCut := [⟨7,21992994,21993005⟩,
⟨64,202620768,202620884⟩]
theorem checked61388 : checkPrefixCuts (2^48) 8050180097 10 Manual.Count131072.C061388.packed 64 cuts61388 = true := by
 decide +kernel
def pointBounds61388 : List (Nat × Nat × Nat) := [(8050194432,114199071942485,114199460511151)]
theorem point_links_checked61388 : (cuts61388.take 1).map (fun c => (8050180097-1+2*2^10*c.k,114199049949491+c.lower,114199438518146+c.upper)) = pointBounds61388 := by
 decide +kernel
def cuts61389 : List PrefixCut := [⟨64,199190979,199191096⟩]
theorem checked61389 : checkPrefixCuts (2^48) 8050311169 10 Manual.Count131072.C061389.packed 64 cuts61389 = true := by
 decide +kernel
def cuts61390 : List PrefixCut := [⟨2,6363429,6363433⟩,
⟨64,202124664,202124780⟩]
theorem checked61390 : checkPrefixCuts (2^48) 8050442241 10 Manual.Count131072.C061390.packed 64 cuts61390 = true := by
 decide +kernel
def pointBounds61390 : List (Nat × Nat × Nat) := [(8050446336,114199458124667,114199846693559)]
theorem point_links_checked61390 : (cuts61390.take 1).map (fun c => (8050442241-1+2*2^10*c.k,114199451761238+c.lower,114199840330126+c.upper)) = pointBounds61390 := by
 decide +kernel
def cuts61391 : List PrefixCut := [⟨61,192191968,192192077⟩,
⟨64,201806732,201806847⟩]
theorem checked61391 : checkPrefixCuts (2^48) 8050573313 10 Manual.Count131072.C061391.packed 64 cuts61391 = true := by
 decide +kernel
def pointBounds61391 : List (Nat × Nat × Nat) := [(8050698240,114199846077870,114200234646983)]
theorem point_links_checked61391 : (cuts61391.take 1).map (fun c => (8050573313-1+2*2^10*c.k,114199653885902+c.lower,114200042454906+c.upper)) = pointBounds61391 := by
 decide +kernel
def cuts61392 : List PrefixCut := [⟨64,201663592,201663709⟩]
theorem checked61392 : checkPrefixCuts (2^48) 8050704385 10 Manual.Count131072.C061392.packed 64 cuts61392 = true := by
 decide +kernel
def cuts61393 : List PrefixCut := [⟨56,175194324,175194425⟩,
⟨64,200331760,200331875⟩]
theorem checked61393 : checkPrefixCuts (2^48) 8050835457 10 Manual.Count131072.C061393.packed 64 cuts61393 = true := by
 decide +kernel
def pointBounds61393 : List (Nat × Nat × Nat) := [(8050950144,114200232550550,114200621119887)]
theorem point_links_checked61393 : (cuts61393.take 1).map (fun c => (8050835457-1+2*2^10*c.k,114200057356226+c.lower,114200445925462+c.upper)) = pointBounds61393 := by
 decide +kernel
def cuts61394 : List PrefixCut := [⟨64,200258571,200258685⟩]
theorem checked61394 : checkPrefixCuts (2^48) 8050966529 10 Manual.Count131072.C061394.packed 64 cuts61394 = true := by
 decide +kernel
def cuts61395 : List PrefixCut := [⟨51,159281553,159281642⟩,
⟨64,200779722,200779836⟩]
theorem checked61395 : checkPrefixCuts (2^48) 8051097601 10 Manual.Count131072.C061395.packed 64 cuts61395 = true := by
 decide +kernel
def pointBounds61395 : List (Nat × Nat × Nat) := [(8051202048,114200617228110,114201005797664)]
theorem point_links_checked61395 : (cuts61395.take 1).map (fun c => (8051097601-1+2*2^10*c.k,114200457946557+c.lower,114200846516022+c.upper)) = pointBounds61395 := by
 decide +kernel
def cuts61396 : List PrefixCut := [⟨64,200951254,200951369⟩]
theorem checked61396 : checkPrefixCuts (2^48) 8051228673 10 Manual.Count131072.C061396.packed 64 cuts61396 = true := by
 decide +kernel
def cuts61397 : List PrefixCut := [⟨46,144103947,144104030⟩,
⟨64,200947981,200948097⟩]
theorem checked61397 : checkPrefixCuts (2^48) 8051359745 10 Manual.Count131072.C061397.packed 64 cuts61397 = true := by
 decide +kernel
def pointBounds61397 : List (Nat × Nat × Nat) := [(8051453952,114201003781480,114201392351257)]
theorem point_links_checked61397 : (cuts61397.take 1).map (fun c => (8051359745-1+2*2^10*c.k,114200859677533+c.lower,114201248247227+c.upper)) = pointBounds61397 := by
 decide +kernel
def cuts61398 : List PrefixCut := [⟨64,200734953,200735068⟩]
theorem checked61398 : checkPrefixCuts (2^48) 8051490817 10 Manual.Count131072.C061398.packed 64 cuts61398 = true := by
 decide +kernel
def cuts61399 : List PrefixCut := [⟨41,127354189,127354262⟩,
⟨64,201081284,201081397⟩]
theorem checked61399 : checkPrefixCuts (2^48) 8051621889 10 Manual.Count131072.C061399.packed 64 cuts61399 = true := by
 decide +kernel
def pointBounds61399 : List (Nat × Nat × Nat) := [(8051705856,114201388714656,114201777284654)]
theorem point_links_checked61399 : (cuts61399.take 1).map (fun c => (8051621889-1+2*2^10*c.k,114201261360467+c.lower,114201649930392+c.upper)) = pointBounds61399 := by
 decide +kernel
def cuts61400 : List PrefixCut := [⟨64,201986904,201987020⟩]
theorem checked61400 : checkPrefixCuts (2^48) 8051752961 10 Manual.Count131072.C061400.packed 64 cuts61400 = true := by
 decide +kernel
def cuts61401 : List PrefixCut := [⟨36,113332166,113332233⟩,
⟨64,202403107,202403226⟩]
theorem checked61401 : checkPrefixCuts (2^48) 8051884033 10 Manual.Count131072.C061401.packed 64 cuts61401 = true := by
 decide +kernel
def pointBounds61401 : List (Nat × Nat × Nat) := [(8051957760,114201777760821,114202166331042)]
theorem point_links_checked61401 : (cuts61401.take 1).map (fun c => (8051884033-1+2*2^10*c.k,114201664428655+c.lower,114202052998809+c.upper)) = pointBounds61401 := by
 decide +kernel
def cuts61402 : List PrefixCut := [⟨64,198100127,198100242⟩]
theorem checked61402 : checkPrefixCuts (2^48) 8052015105 10 Manual.Count131072.C061402.packed 64 cuts61402 = true := by
 decide +kernel
def cuts61403 : List PrefixCut := [⟨31,97108789,97108844⟩,
⟨64,202571295,202571407⟩]
theorem checked61403 : checkPrefixCuts (2^48) 8052146177 10 Manual.Count131072.C061403.packed 64 cuts61403 = true := by
 decide +kernel
def pointBounds61403 : List (Nat × Nat × Nat) := [(8052209664,114202162040678,114202550611121)]
theorem point_links_checked61403 : (cuts61403.take 1).map (fun c => (8052146177-1+2*2^10*c.k,114202064931889+c.lower,114202453502277+c.upper)) = pointBounds61403 := by
 decide +kernel
def cuts61404 : List PrefixCut := [⟨64,200960041,200960162⟩]
theorem checked61404 : checkPrefixCuts (2^48) 8052277249 10 Manual.Count131072.C061404.packed 64 cuts61404 = true := by
 decide +kernel
def cuts61405 : List PrefixCut := [⟨26,81166096,81166142⟩,
⟨64,201096592,201096703⟩]
theorem checked61405 : checkPrefixCuts (2^48) 8052408321 10 Manual.Count131072.C061405.packed 64 cuts61405 = true := by
 decide +kernel
def pointBounds61405 : List (Nat × Nat × Nat) := [(8052461568,114202549629321,114202938199988)]
theorem point_links_checked61405 : (cuts61405.take 1).map (fun c => (8052408321-1+2*2^10*c.k,114202468463225+c.lower,114202857033846+c.upper)) = pointBounds61405 := by
 decide +kernel
def cuts61406 : List PrefixCut := [⟨64,199660189,199660301⟩]
theorem checked61406 : checkPrefixCuts (2^48) 8052539393 10 Manual.Count131072.C061406.packed 64 cuts61406 = true := by
 decide +kernel
def cuts61407 : List PrefixCut := [⟨21,66063319,66063358⟩,
⟨64,201789128,201789243⟩]
theorem checked61407 : checkPrefixCuts (2^48) 8052670465 10 Manual.Count131072.C061407.packed 64 cuts61407 = true := by
 decide +kernel
def pointBounds61407 : List (Nat × Nat × Nat) := [(8052713472,114202935283325,114203323854208)]
theorem point_links_checked61407 : (cuts61407.take 1).map (fun c => (8052670465-1+2*2^10*c.k,114202869220006+c.lower,114203257790850+c.upper)) = pointBounds61407 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000043
