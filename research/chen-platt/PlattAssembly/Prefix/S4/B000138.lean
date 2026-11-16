import PlattAssemblyKernel
import PlattCertificates.Count131072.C034416
import PlattCertificates.Count131072.C034417
import PlattCertificates.Count131072.C034418
import PlattCertificates.Count131072.C034419
import PlattCertificates.Count131072.C034420
import PlattCertificates.Count131072.C034421
import PlattCertificates.Count131072.C034422
import PlattCertificates.Count131072.C034423
import PlattCertificates.Count131072.C034424
import PlattCertificates.Count131072.C034425
import PlattCertificates.Count131072.C034426
import PlattCertificates.Count131072.C034427
import PlattCertificates.Count131072.C034428
import PlattCertificates.Count131072.C034429
import PlattCertificates.Count131072.C034430
import PlattCertificates.Count131072.C034431
import PlattCertificates.Count131072.C034432
import PlattCertificates.Count131072.C034433
import PlattCertificates.Count131072.C034434
import PlattCertificates.Count131072.C034435
import PlattCertificates.Count131072.C034436
import PlattCertificates.Count131072.C034437
import PlattCertificates.Count131072.C034438
import PlattCertificates.Count131072.C034439
import PlattCertificates.Count131072.C034440
import PlattCertificates.Count131072.C034441
import PlattCertificates.Count131072.C034442
import PlattCertificates.Count131072.C034443
import PlattCertificates.Count131072.C034444
import PlattCertificates.Count131072.C034445
import PlattCertificates.Count131072.C034446
import PlattCertificates.Count131072.C034447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000138
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts34416 : List PrefixCut := [⟨64,362397335,362397564⟩]
theorem checked34416 : checkPrefixCuts (2^48) 4514906113 10 Manual.Count131072.C034416.packed 64 cuts34416 = true := by
 decide +kernel
def cuts34417 : List PrefixCut := [⟨3,17143944,17143954⟩,
⟨64,369057273,369057506⟩]
theorem checked34417 : checkPrefixCuts (2^48) 4515037185 10 Manual.Count131072.C034417.packed 64 cuts34417 = true := by
 decide +kernel
def pointBounds34417 : List (Nat × Nat × Nat) := [(4515043328,106970790412417,106971174762096)]
theorem point_links_checked34417 : (cuts34417.take 1).map (fun c => (4515037185-1+2*2^10*c.k,106970773268473+c.lower,106971157618142+c.upper)) = pointBounds34417 := by
 decide +kernel
def cuts34418 : List PrefixCut := [⟨8,47814576,47814606⟩,
⟨64,369607563,369607792⟩]
theorem checked34418 : checkPrefixCuts (2^48) 4515168257 10 Manual.Count131072.C034418.packed 64 cuts34418 = true := by
 decide +kernel
def pointBounds34418 : List (Nat × Nat × Nat) := [(4515184640,106971190140322,106971574490254)]
theorem point_links_checked34418 : (cuts34418.take 1).map (fun c => (4515168257-1+2*2^10*c.k,106971142325746+c.lower,106971526675648+c.upper)) = pointBounds34418 := by
 decide +kernel
def cuts34419 : List PrefixCut := [⟨13,75428803,75428848⟩,
⟨64,369160488,369160716⟩]
theorem checked34419 : checkPrefixCuts (2^48) 4515299329 10 Manual.Count131072.C034419.packed 64 cuts34419 = true := by
 decide +kernel
def pointBounds34419 : List (Nat × Nat × Nat) := [(4515325952,106971587362112,106971971712288)]
theorem point_links_checked34419 : (cuts34419.take 1).map (fun c => (4515299329-1+2*2^10*c.k,106971511933309+c.lower,106971896283440+c.upper)) = pointBounds34419 := by
 decide +kernel
def cuts34420 : List PrefixCut := [⟨18,102417999,102418065⟩,
⟨64,368651087,368651319⟩]
theorem checked34420 : checkPrefixCuts (2^48) 4515430401 10 Manual.Count131072.C034420.packed 64 cuts34420 = true := by
 decide +kernel
def pointBounds34420 : List (Nat × Nat × Nat) := [(4515467264,106971983511796,106972367862221)]
theorem point_links_checked34420 : (cuts34420.take 1).map (fun c => (4515430401-1+2*2^10*c.k,106971881093797+c.lower,106972265444156+c.upper)) = pointBounds34420 := by
 decide +kernel
def cuts34421 : List PrefixCut := [⟨23,131711929,131712012⟩,
⟨64,369513045,369513275⟩]
theorem checked34421 : checkPrefixCuts (2^48) 4515561473 10 Manual.Count131072.C034421.packed 64 cuts34421 = true := by
 decide +kernel
def pointBounds34421 : List (Nat × Nat × Nat) := [(4515608576,106972381456813,106972765807487)]
theorem point_links_checked34421 : (cuts34421.take 1).map (fun c => (4515561473-1+2*2^10*c.k,106972249744884+c.lower,106972634095475+c.upper)) = pointBounds34421 := by
 decide +kernel
def cuts34422 : List PrefixCut := [⟨28,160069136,160069235⟩,
⟨64,366697405,366697633⟩]
theorem checked34422 : checkPrefixCuts (2^48) 4515692545 10 Manual.Count131072.C034422.packed 64 cuts34422 = true := by
 decide +kernel
def pointBounds34422 : List (Nat × Nat × Nat) := [(4515749888,106972779327065,106973163677985)]
theorem point_links_checked34422 : (cuts34422.take 1).map (fun c => (4515692545-1+2*2^10*c.k,106972619257929+c.lower,106973003608750+c.upper)) = pointBounds34422 := by
 decide +kernel
def cuts34423 : List PrefixCut := [⟨33,188798558,188798678⟩,
⟨64,367496995,367497227⟩]
theorem checked34423 : checkPrefixCuts (2^48) 4515823617 10 Manual.Count131072.C034423.packed 64 cuts34423 = true := by
 decide +kernel
def pointBounds34423 : List (Nat × Nat × Nat) := [(4515891200,106973174753892,106973559105061)]
theorem point_links_checked34423 : (cuts34423.take 1).map (fun c => (4515823617-1+2*2^10*c.k,106972985955334+c.lower,106973370306383+c.upper)) = pointBounds34423 := by
 decide +kernel
def cuts34424 : List PrefixCut := [⟨38,219957112,219957248⟩,
⟨64,368483666,368483896⟩]
theorem checked34424 : checkPrefixCuts (2^48) 4515954689 10 Manual.Count131072.C034424.packed 64 cuts34424 = true := by
 decide +kernel
def pointBounds34424 : List (Nat × Nat × Nat) := [(4516032512,106973573409441,106973957760858)]
theorem point_links_checked34424 : (cuts34424.take 1).map (fun c => (4515954689-1+2*2^10*c.k,106973353452329+c.lower,106973737803610+c.upper)) = pointBounds34424 := by
 decide +kernel
def cuts34425 : List PrefixCut := [⟨43,251923997,251924155⟩,
⟨64,371713932,371714163⟩]
theorem checked34425 : checkPrefixCuts (2^48) 4516085761 10 Manual.Count131072.C034425.packed 64 cuts34425 = true := by
 decide +kernel
def pointBounds34425 : List (Nat × Nat × Nat) := [(4516173824,106973973859992,106974358211661)]
theorem point_links_checked34425 : (cuts34425.take 1).map (fun c => (4516085761-1+2*2^10*c.k,106973721935995+c.lower,106974106287506+c.upper)) = pointBounds34425 := by
 decide +kernel
def cuts34426 : List PrefixCut := [⟨48,275475140,275475312⟩,
⟨64,369521736,369521965⟩]
theorem checked34426 : checkPrefixCuts (2^48) 4516216833 10 Manual.Count131072.C034426.packed 64 cuts34426 = true := by
 decide +kernel
def pointBounds34426 : List (Nat × Nat × Nat) := [(4516315136,106974369125067,106974753476981)]
theorem point_links_checked34426 : (cuts34426.take 1).map (fun c => (4516216833-1+2*2^10*c.k,106974093649927+c.lower,106974478001669+c.upper)) = pointBounds34426 := by
 decide +kernel
def cuts34427 : List PrefixCut := [⟨53,302203339,302203530⟩,
⟨64,363341130,363341362⟩]
theorem checked34427 : checkPrefixCuts (2^48) 4516347905 10 Manual.Count131072.C034427.packed 64 cuts34427 = true := by
 decide +kernel
def pointBounds34427 : List (Nat × Nat × Nat) := [(4516456448,106974765375002,106975149727164)]
theorem point_links_checked34427 : (cuts34427.take 1).map (fun c => (4516347905-1+2*2^10*c.k,106974463171663+c.lower,106974847523634+c.upper)) = pointBounds34427 := by
 decide +kernel
def cuts34428 : List PrefixCut := [⟨58,330363271,330363480⟩,
⟨64,363392885,363393116⟩]
theorem checked34428 : checkPrefixCuts (2^48) 4516478977 10 Manual.Count131072.C034428.packed 64 cuts34428 = true := by
 decide +kernel
def pointBounds34428 : List (Nat × Nat × Nat) := [(4516597760,106975156876064,106975541228476)]
theorem point_links_checked34428 : (cuts34428.take 1).map (fun c => (4516478977-1+2*2^10*c.k,106974826512793+c.lower,106975210864996+c.upper)) = pointBounds34428 := by
 decide +kernel
def cuts34429 : List PrefixCut := [⟨63,360702694,360702923⟩,
⟨64,366809873,366810106⟩]
theorem checked34429 : checkPrefixCuts (2^48) 4516610049 10 Manual.Count131072.C034429.packed 64 cuts34429 = true := by
 decide +kernel
def pointBounds34429 : List (Nat × Nat × Nat) := [(4516739072,106975550608372,106975934961035)]
theorem point_links_checked34429 : (cuts34429.take 1).map (fun c => (4516610049-1+2*2^10*c.k,106975189905678+c.lower,106975574258112+c.upper)) = pointBounds34429 := by
 decide +kernel
def cuts34430 : List PrefixCut := [⟨64,367484716,367484950⟩]
theorem checked34430 : checkPrefixCuts (2^48) 4516741121 10 Manual.Count131072.C034430.packed 64 cuts34430 = true := by
 decide +kernel
def cuts34431 : List PrefixCut := [⟨4,22184592,22184607⟩,
⟨64,368034889,368035126⟩]
theorem checked34431 : checkPrefixCuts (2^48) 4516872193 10 Manual.Count131072.C034431.packed 64 cuts34431 = true := by
 decide +kernel
def pointBounds34431 : List (Nat × Nat × Nat) := [(4516880384,106975946384859,106976330737775)]
theorem point_links_checked34431 : (cuts34431.take 1).map (fun c => (4516872193-1+2*2^10*c.k,106975924200267+c.lower,106976308553168+c.upper)) = pointBounds34431 := by
 decide +kernel
def cuts34432 : List PrefixCut := [⟨9,51596316,51596350⟩,
⟨64,370766026,370766259⟩]
theorem checked34432 : checkPrefixCuts (2^48) 4517003265 10 Manual.Count131072.C034432.packed 64 cuts34432 = true := by
 decide +kernel
def pointBounds34432 : List (Nat × Nat × Nat) := [(4517021696,106976343831472,106976728184644)]
theorem point_links_checked34432 : (cuts34432.take 1).map (fun c => (4517003265-1+2*2^10*c.k,106976292235156+c.lower,106976676588294+c.upper)) = pointBounds34432 := by
 decide +kernel
def cuts34433 : List PrefixCut := [⟨14,79635394,79635446⟩,
⟨64,365957209,365957440⟩]
theorem checked34433 : checkPrefixCuts (2^48) 4517134337 10 Manual.Count131072.C034433.packed 64 cuts34433 = true := by
 decide +kernel
def pointBounds34433 : List (Nat × Nat × Nat) := [(4517163008,106976742636576,106977126989999)]
theorem point_links_checked34433 : (cuts34433.take 1).map (fun c => (4517134337-1+2*2^10*c.k,106976663001182+c.lower,106977047354553+c.upper)) = pointBounds34433 := by
 decide +kernel
def cuts34434 : List PrefixCut := [⟨19,106925054,106925121⟩,
⟨64,368065108,368065338⟩]
theorem checked34434 : checkPrefixCuts (2^48) 4517265409 10 Manual.Count131072.C034434.packed 64 cuts34434 = true := by
 decide +kernel
def pointBounds34434 : List (Nat × Nat × Nat) := [(4517304320,106977135883445,106977520237114)]
theorem point_links_checked34434 : (cuts34434.take 1).map (fun c => (4517265409-1+2*2^10*c.k,106977028958391+c.lower,106977413311993+c.upper)) = pointBounds34434 := by
 decide +kernel
def cuts34435 : List PrefixCut := [⟨24,139135456,139135545⟩,
⟨64,370920645,370920876⟩]
theorem checked34435 : checkPrefixCuts (2^48) 4517396481 10 Manual.Count131072.C034435.packed 64 cuts34435 = true := by
 decide +kernel
def pointBounds34435 : List (Nat × Nat × Nat) := [(4517445632,106977536158955,106977920512876)]
theorem point_links_checked34435 : (cuts34435.take 1).map (fun c => (4517396481-1+2*2^10*c.k,106977397023499+c.lower,106977781377331+c.upper)) = pointBounds34435 := by
 decide +kernel
def cuts34436 : List PrefixCut := [⟨29,164614772,164614881⟩,
⟨64,367358398,367358631⟩]
theorem checked34436 : checkPrefixCuts (2^48) 4517527553 10 Manual.Count131072.C034436.packed 64 cuts34436 = true := by
 decide +kernel
def pointBounds34436 : List (Nat × Nat × Nat) := [(4517586944,106977932558916,106978316913088)]
theorem point_links_checked34436 : (cuts34436.take 1).map (fun c => (4517527553-1+2*2^10*c.k,106977767944144+c.lower,106978152298207+c.upper)) = pointBounds34436 := by
 decide +kernel
def cuts34437 : List PrefixCut := [⟨34,188597224,188597340⟩,
⟨64,361117259,361117481⟩]
theorem checked34437 : checkPrefixCuts (2^48) 4517658625 10 Manual.Count131072.C034437.packed 64 cuts34437 = true := by
 decide +kernel
def pointBounds34437 : List (Nat × Nat × Nat) := [(4517728256,106978323899766,106978708254178)]
theorem point_links_checked34437 : (cuts34437.take 1).map (fun c => (4517658625-1+2*2^10*c.k,106978135302542+c.lower,106978519656838+c.upper)) = pointBounds34437 := by
 decide +kernel
def cuts34438 : List PrefixCut := [⟨39,222484467,222484601⟩,
⟨64,361792229,361792452⟩]
theorem checked34438 : checkPrefixCuts (2^48) 4517789697 10 Manual.Count131072.C034438.packed 64 cuts34438 = true := by
 decide +kernel
def pointBounds34438 : List (Nat × Nat × Nat) := [(4517869568,106978718904268,106979103258920)]
theorem point_links_checked34438 : (cuts34438.take 1).map (fun c => (4517789697-1+2*2^10*c.k,106978496419801+c.lower,106978880774319+c.upper)) = pointBounds34438 := by
 decide +kernel
def cuts34439 : List PrefixCut := [⟨44,253752956,253753122⟩,
⟨64,369382396,369382636⟩]
theorem checked34439 : checkPrefixCuts (2^48) 4517920769 10 Manual.Count131072.C034439.packed 64 cuts34439 = true := by
 decide +kernel
def pointBounds34439 : List (Nat × Nat × Nat) := [(4518010880,106979111964986,106979496319893)]
theorem point_links_checked34439 : (cuts34439.take 1).map (fun c => (4517920769-1+2*2^10*c.k,106978858212030+c.lower,106979242566771+c.upper)) = pointBounds34439 := by
 decide +kernel
def cuts34440 : List PrefixCut := [⟨49,279661836,279662008⟩,
⟨64,366568189,366568416⟩]
theorem checked34440 : checkPrefixCuts (2^48) 4518051841 10 Manual.Count131072.C034440.packed 64 cuts34440 = true := by
 decide +kernel
def pointBounds34440 : List (Nat × Nat × Nat) := [(4518152192,106979507256262,106979891611415)]
theorem point_links_checked34440 : (cuts34440.take 1).map (fun c => (4518051841-1+2*2^10*c.k,106979227594426+c.lower,106979611949407+c.upper)) = pointBounds34440 := by
 decide +kernel
def cuts34441 : List PrefixCut := [⟨54,308434869,308435057⟩,
⟨64,366619879,366620101⟩]
theorem checked34441 : checkPrefixCuts (2^48) 4518182913 10 Manual.Count131072.C034441.packed 64 cuts34441 = true := by
 decide +kernel
def pointBounds34441 : List (Nat × Nat × Nat) := [(4518293504,106979902597484,106980286952880)]
theorem point_links_checked34441 : (cuts34441.take 1).map (fun c => (4518182913-1+2*2^10*c.k,106979594162615+c.lower,106979978517823+c.upper)) = pointBounds34441 := by
 decide +kernel
def cuts34442 : List PrefixCut := [⟨59,337455328,337455540⟩,
⟨64,365238766,365238996⟩]
theorem checked34442 : checkPrefixCuts (2^48) 4518313985 10 Manual.Count131072.C034442.packed 64 cuts34442 = true := by
 decide +kernel
def pointBounds34442 : List (Nat × Nat × Nat) := [(4518434816,106980298237822,106980682593464)]
theorem point_links_checked34442 : (cuts34442.take 1).map (fun c => (4518313985-1+2*2^10*c.k,106979960782494+c.lower,106980345137924+c.upper)) = pointBounds34442 := by
 decide +kernel
def cuts34443 : List PrefixCut := [⟨64,366100260,366100489⟩]
theorem checked34443 : checkPrefixCuts (2^48) 4518445057 10 Manual.Count131072.C034443.packed 64 cuts34443 = true := by
 decide +kernel
def pointBounds34443 : List (Nat × Nat × Nat) := [(4518576128,106980692121520,106981076477409)]
theorem point_links_checked34443 : (cuts34443.take 1).map (fun c => (4518445057-1+2*2^10*c.k,106980326021260+c.lower,106980710376920+c.upper)) = pointBounds34443 := by
 decide +kernel
def cuts34444 : List PrefixCut := [⟨64,371384451,371384681⟩]
theorem checked34444 : checkPrefixCuts (2^48) 4518576129 10 Manual.Count131072.C034444.packed 64 cuts34444 = true := by
 decide +kernel
def cuts34445 : List PrefixCut := [⟨5,27657182,27657200⟩,
⟨64,365269241,365269468⟩]
theorem checked34445 : checkPrefixCuts (2^48) 4518707201 10 Manual.Count131072.C034445.packed 64 cuts34445 = true := by
 decide +kernel
def pointBounds34445 : List (Nat × Nat × Nat) := [(4518717440,106981091163153,106981475519290)]
theorem point_links_checked34445 : (cuts34445.take 1).map (fun c => (4518707201-1+2*2^10*c.k,106981063505971+c.lower,106981447862090+c.upper)) = pointBounds34445 := by
 decide +kernel
def cuts34446 : List PrefixCut := [⟨10,57305947,57305985⟩,
⟨64,372234927,372235164⟩]
theorem checked34446 : checkPrefixCuts (2^48) 4518838273 10 Manual.Count131072.C034446.packed 64 cuts34446 = true := by
 decide +kernel
def pointBounds34446 : List (Nat × Nat × Nat) := [(4518858752,106981486081159,106981870437543)]
theorem point_links_checked34446 : (cuts34446.take 1).map (fun c => (4518838273-1+2*2^10*c.k,106981428775212+c.lower,106981813131558+c.upper)) = pointBounds34446 := by
 decide +kernel
def cuts34447 : List PrefixCut := [⟨15,85707181,85707235⟩,
⟨64,371476717,371476948⟩]
theorem checked34447 : checkPrefixCuts (2^48) 4518969345 10 Manual.Count131072.C034447.packed 64 cuts34447 = true := by
 decide +kernel
def pointBounds34447 : List (Nat × Nat × Nat) := [(4519000064,106981886717320,106982271073957)]
theorem point_links_checked34447 : (cuts34447.take 1).map (fun c => (4518969345-1+2*2^10*c.k,106981801010139+c.lower,106982185366722+c.upper)) = pointBounds34447 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000138
