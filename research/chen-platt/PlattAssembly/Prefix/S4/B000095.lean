import PlattAssemblyKernel
import PlattCertificates.Count131072.C033040
import PlattCertificates.Count131072.C033041
import PlattCertificates.Count131072.C033042
import PlattCertificates.Count131072.C033043
import PlattCertificates.Count131072.C033044
import PlattCertificates.Count131072.C033045
import PlattCertificates.Count131072.C033046
import PlattCertificates.Count131072.C033047
import PlattCertificates.Count131072.C033048
import PlattCertificates.Count131072.C033049
import PlattCertificates.Count131072.C033050
import PlattCertificates.Count131072.C033051
import PlattCertificates.Count131072.C033052
import PlattCertificates.Count131072.C033053
import PlattCertificates.Count131072.C033054
import PlattCertificates.Count131072.C033055
import PlattCertificates.Count131072.C033056
import PlattCertificates.Count131072.C033057
import PlattCertificates.Count131072.C033058
import PlattCertificates.Count131072.C033059
import PlattCertificates.Count131072.C033060
import PlattCertificates.Count131072.C033061
import PlattCertificates.Count131072.C033062
import PlattCertificates.Count131072.C033063
import PlattCertificates.Count131072.C033064
import PlattCertificates.Count131072.C033065
import PlattCertificates.Count131072.C033066
import PlattCertificates.Count131072.C033067
import PlattCertificates.Count131072.C033068
import PlattCertificates.Count131072.C033069
import PlattCertificates.Count131072.C033070
import PlattCertificates.Count131072.C033071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts33040 : List PrefixCut := [⟨64,385398193,385398440⟩]
theorem checked33040 : checkPrefixCuts (2^48) 4334551041 10 Manual.Count131072.C033040.packed 64 cuts33040 = true := by
 decide +kernel
def cuts33041 : List PrefixCut := [⟨3,18831291,18831303⟩,
⟨64,387529416,387529663⟩]
theorem checked33041 : checkPrefixCuts (2^48) 4334682113 10 Manual.Count131072.C033041.packed 64 cuts33041 = true := by
 decide +kernel
def pointBounds33041 : List (Nat × Nat × Nat) := [(4334688256,106454186675994,106454570698521)]
theorem point_links_checked33041 : (cuts33041.take 1).map (fun c => (4334682113-1+2*2^10*c.k,106454167844703+c.lower,106454551867218+c.upper)) = pointBounds33041 := by
 decide +kernel
def cuts33042 : List PrefixCut := [⟨6,36622480,36622503⟩,
⟨64,382258120,382258362⟩]
theorem checked33042 : checkPrefixCuts (2^48) 4334813185 10 Manual.Count131072.C033042.packed 64 cuts33042 = true := by
 decide +kernel
def pointBounds33042 : List (Nat × Nat × Nat) := [(4334825472,106454591996599,106454976019384)]
theorem point_links_checked33042 : (cuts33042.take 1).map (fun c => (4334813185-1+2*2^10*c.k,106454555374119+c.lower,106454939396881+c.upper)) = pointBounds33042 := by
 decide +kernel
def cuts33043 : List PrefixCut := [⟨9,57074757,57074794⟩,
⟨64,387376114,387376362⟩]
theorem checked33043 : checkPrefixCuts (2^48) 4334944257 10 Manual.Count131072.C033043.packed 64 cuts33043 = true := by
 decide +kernel
def pointBounds33043 : List (Nat × Nat × Nat) := [(4334962688,106454994706996,106455378730037)]
theorem point_links_checked33043 : (cuts33043.take 1).map (fun c => (4334944257-1+2*2^10*c.k,106454937632239+c.lower,106455321655243+c.upper)) = pointBounds33043 := by
 decide +kernel
def cuts33044 : List PrefixCut := [⟨12,72656062,72656108⟩,
⟨64,386715137,386715387⟩]
theorem checked33044 : checkPrefixCuts (2^48) 4335075329 10 Manual.Count131072.C033044.packed 64 cuts33044 = true := by
 decide +kernel
def pointBounds33044 : List (Nat × Nat × Nat) := [(4335099904,106455397664415,106455781687713)]
theorem point_links_checked33044 : (cuts33044.take 1).map (fun c => (4335075329-1+2*2^10*c.k,106455325008353+c.lower,106455709031605+c.upper)) = pointBounds33044 := by
 decide +kernel
def cuts33045 : List PrefixCut := [⟨15,86613218,86613273⟩,
⟨64,379496495,379496739⟩]
theorem checked33045 : checkPrefixCuts (2^48) 4335206401 10 Manual.Count131072.C033045.packed 64 cuts33045 = true := by
 decide +kernel
def pointBounds33045 : List (Nat × Nat × Nat) := [(4335237120,106455798336708,106456182360265)]
theorem point_links_checked33045 : (cuts33045.take 1).map (fun c => (4335206401-1+2*2^10*c.k,106455711723490+c.lower,106456095746992+c.upper)) = pointBounds33045 := by
 decide +kernel
def cuts33046 : List PrefixCut := [⟨18,105309070,105309138⟩,
⟨64,376498556,376498802⟩]
theorem checked33046 : checkPrefixCuts (2^48) 4335337473 10 Manual.Count131072.C033046.packed 64 cuts33046 = true := by
 decide +kernel
def pointBounds33046 : List (Nat × Nat × Nat) := [(4335374336,106456196529055,106456580552869)]
theorem point_links_checked33046 : (cuts33046.take 1).map (fun c => (4335337473-1+2*2^10*c.k,106456091219985+c.lower,106456475243731+c.upper)) = pointBounds33046 := by
 decide +kernel
def cuts33047 : List PrefixCut := [⟨21,123029905,123029984⟩,
⟨64,382200322,382200565⟩]
theorem checked33047 : checkPrefixCuts (2^48) 4335468545 10 Manual.Count131072.C033047.packed 64 cuts33047 = true := by
 decide +kernel
def pointBounds33047 : List (Nat × Nat × Nat) := [(4335511552,106456590748446,106456974772517)]
theorem point_links_checked33047 : (cuts33047.take 1).map (fun c => (4335468545-1+2*2^10*c.k,106456467718541+c.lower,106456851742533+c.upper)) = pointBounds33047 := by
 decide +kernel
def cuts33048 : List PrefixCut := [⟨24,143476339,143476428⟩,
⟨64,382383517,382383763⟩]
theorem checked33048 : checkPrefixCuts (2^48) 4335599617 10 Manual.Count131072.C033048.packed 64 cuts33048 = true := by
 decide +kernel
def pointBounds33048 : List (Nat × Nat × Nat) := [(4335648768,106456993395202,106457377419526)]
theorem point_links_checked33048 : (cuts33048.take 1).map (fun c => (4335599617-1+2*2^10*c.k,106456849918863+c.lower,106457233943098+c.upper)) = pointBounds33048 := by
 decide +kernel
def cuts33049 : List PrefixCut := [⟨27,163337236,163337342⟩,
⟨64,384644163,384644410⟩]
theorem checked33049 : checkPrefixCuts (2^48) 4335730689 10 Manual.Count131072.C033049.packed 64 cuts33049 = true := by
 decide +kernel
def pointBounds33049 : List (Nat × Nat × Nat) := [(4335785984,106457395639616,106457779664203)]
theorem point_links_checked33049 : (cuts33049.take 1).map (fun c => (4335730689-1+2*2^10*c.k,106457232302380+c.lower,106457616326861+c.upper)) = pointBounds33049 := by
 decide +kernel
def cuts33050 : List PrefixCut := [⟨30,180989722,180989840⟩,
⟨64,380672649,380672892⟩]
theorem checked33050 : checkPrefixCuts (2^48) 4335861761 10 Manual.Count131072.C033050.packed 64 cuts33050 = true := by
 decide +kernel
def pointBounds33050 : List (Nat × Nat × Nat) := [(4335923200,106457797936265,106458181961111)]
theorem point_links_checked33050 : (cuts33050.take 1).map (fun c => (4335861761-1+2*2^10*c.k,106457616946543+c.lower,106458000971271+c.upper)) = pointBounds33050 := by
 decide +kernel
def cuts33051 : List PrefixCut := [⟨33,198446372,198446499⟩,
⟨64,387022744,387022992⟩]
theorem checked33051 : checkPrefixCuts (2^48) 4335992833 10 Manual.Count131072.C033051.packed 64 cuts33051 = true := by
 decide +kernel
def pointBounds33051 : List (Nat × Nat × Nat) := [(4336060416,106458196065564,106458580090662)]
theorem point_links_checked33051 : (cuts33051.take 1).map (fun c => (4335992833-1+2*2^10*c.k,106457997619192+c.lower,106458381644163+c.upper)) = pointBounds33051 := by
 decide +kernel
def cuts33052 : List PrefixCut := [⟨36,217589671,217589806⟩,
⟨64,385582974,385583221⟩]
theorem checked33052 : checkPrefixCuts (2^48) 4336123905 10 Manual.Count131072.C033052.packed 64 cuts33052 = true := by
 decide +kernel
def pointBounds33052 : List (Nat × Nat × Nat) := [(4336197632,106458602231607,106458986256961)]
theorem point_links_checked33052 : (cuts33052.take 1).map (fun c => (4336123905-1+2*2^10*c.k,106458384641936+c.lower,106458768667155+c.upper)) = pointBounds33052 := by
 decide +kernel
def cuts33053 : List PrefixCut := [⟨39,232382727,232382877⟩,
⟨64,382195931,382196176⟩]
theorem checked33053 : checkPrefixCuts (2^48) 4336254977 10 Manual.Count131072.C033053.packed 64 cuts33053 = true := by
 decide +kernel
def pointBounds33053 : List (Nat × Nat × Nat) := [(4336334848,106459002607637,106459386633253)]
theorem point_links_checked33053 : (cuts33053.take 1).map (fun c => (4336254977-1+2*2^10*c.k,106458770224910+c.lower,106459154250376+c.upper)) = pointBounds33053 := by
 decide +kernel
def cuts33054 : List PrefixCut := [⟨42,253016742,253016901⟩,
⟨64,383287887,383288128⟩]
theorem checked33054 : checkPrefixCuts (2^48) 4336386049 10 Manual.Count131072.C033054.packed 64 cuts33054 = true := by
 decide +kernel
def pointBounds33054 : List (Nat × Nat × Nat) := [(4336472064,106459405437583,106459789463453)]
theorem point_links_checked33054 : (cuts33054.take 1).map (fun c => (4336386049-1+2*2^10*c.k,106459152420841+c.lower,106459536446552+c.upper)) = pointBounds33054 := by
 decide +kernel
def cuts33055 : List PrefixCut := [⟨45,267093760,267093927⟩,
⟨64,381653522,381653761⟩]
theorem checked33055 : checkPrefixCuts (2^48) 4336517121 10 Manual.Count131072.C033055.packed 64 cuts33055 = true := by
 decide +kernel
def pointBounds33055 : List (Nat × Nat × Nat) := [(4336609280,106459802802488,106460186828607)]
theorem point_links_checked33055 : (cuts33055.take 1).map (fun c => (4336517121-1+2*2^10*c.k,106459535708728+c.lower,106459919734680+c.upper)) = pointBounds33055 := by
 decide +kernel
def cuts33056 : List PrefixCut := [⟨48,292074100,292074286⟩,
⟨64,383459460,383459707⟩]
theorem checked33056 : checkPrefixCuts (2^48) 4336648193 10 Manual.Count131072.C033056.packed 64 cuts33056 = true := by
 decide +kernel
def pointBounds33056 : List (Nat × Nat × Nat) := [(4336746496,106460209436350,106460593462727)]
theorem point_links_checked33056 : (cuts33056.take 1).map (fun c => (4336648193-1+2*2^10*c.k,106459917362250+c.lower,106460301388441+c.upper)) = pointBounds33056 := by
 decide +kernel
def cuts33057 : List PrefixCut := [⟨51,307317383,307317582⟩,
⟨64,384810810,384811057⟩]
theorem checked33057 : checkPrefixCuts (2^48) 4336779265 10 Manual.Count131072.C033057.packed 64 cuts33057 = true := by
 decide +kernel
def pointBounds33057 : List (Nat × Nat × Nat) := [(4336883712,106460608139093,106460992165730)]
theorem point_links_checked33057 : (cuts33057.take 1).map (fun c => (4336779265-1+2*2^10*c.k,106460300821710+c.lower,106460684848148+c.upper)) = pointBounds33057 := by
 decide +kernel
def cuts33058 : List PrefixCut := [⟨54,321391434,321391643⟩,
⟨64,380905063,380905309⟩]
theorem checked33058 : checkPrefixCuts (2^48) 4336910337 10 Manual.Count131072.C033058.packed 64 cuts33058 = true := by
 decide +kernel
def pointBounds33058 : List (Nat × Nat × Nat) := [(4337020928,106461007023954,106461391050848)]
theorem point_links_checked33058 : (cuts33058.take 1).map (fun c => (4336910337-1+2*2^10*c.k,106460685632520+c.lower,106461069659205+c.upper)) = pointBounds33058 := by
 decide +kernel
def cuts33059 : List PrefixCut := [⟨57,342992999,342993216⟩,
⟨64,385436522,385436766⟩]
theorem checked33059 : checkPrefixCuts (2^48) 4337041409 10 Manual.Count131072.C033059.packed 64 cuts33059 = true := by
 decide +kernel
def pointBounds33059 : List (Nat × Nat × Nat) := [(4337158144,106461409530582,106461793557730)]
theorem point_links_checked33059 : (cuts33059.take 1).map (fun c => (4337041409-1+2*2^10*c.k,106461066537583+c.lower,106461450564514+c.upper)) = pointBounds33059 := by
 decide +kernel
def cuts33060 : List PrefixCut := [⟨60,363295250,363295480⟩,
⟨64,388280343,388280589⟩]
theorem checked33060 : checkPrefixCuts (2^48) 4337172481 10 Manual.Count131072.C033060.packed 64 cuts33060 = true := by
 decide +kernel
def pointBounds33060 : List (Nat × Nat × Nat) := [(4337295360,106461815269355,106462199296760)]
theorem point_links_checked33060 : (cuts33060.take 1).map (fun c => (4337172481-1+2*2^10*c.k,106461451974105+c.lower,106461836001280+c.upper)) = pointBounds33060 := by
 decide +kernel
def cuts33061 : List PrefixCut := [⟨63,373407676,373407912⟩,
⟨64,379962004,379962244⟩]
theorem checked33061 : checkPrefixCuts (2^48) 4337303553 10 Manual.Count131072.C033061.packed 64 cuts33061 = true := by
 decide +kernel
def pointBounds33061 : List (Nat × Nat × Nat) := [(4337432576,106462213662124,106462597689781)]
theorem point_links_checked33061 : (cuts33061.take 1).map (fun c => (4337303553-1+2*2^10*c.k,106461840254448+c.lower,106462224281869+c.upper)) = pointBounds33061 := by
 decide +kernel
def cuts33062 : List PrefixCut := [⟨64,384752682,384752928⟩]
theorem checked33062 : checkPrefixCuts (2^48) 4337434625 10 Manual.Count131072.C033062.packed 64 cuts33062 = true := by
 decide +kernel
def cuts33063 : List PrefixCut := [⟨2,10901912,10901920⟩,
⟨64,378706078,378706319⟩]
theorem checked33063 : checkPrefixCuts (2^48) 4337565697 10 Manual.Count131072.C033063.packed 64 cuts33063 = true := by
 decide +kernel
def pointBounds33063 : List (Nat × Nat × Nat) := [(4337569792,106462615871046,106462999898961)]
theorem point_links_checked33063 : (cuts33063.take 1).map (fun c => (4337565697-1+2*2^10*c.k,106462604969134+c.lower,106462988997041+c.upper)) = pointBounds33063 := by
 decide +kernel
def cuts33064 : List PrefixCut := [⟨5,28551742,28551762⟩,
⟨64,383820879,383821131⟩]
theorem checked33064 : checkPrefixCuts (2^48) 4337696769 10 Manual.Count131072.C033064.packed 64 cuts33064 = true := by
 decide +kernel
def pointBounds33064 : List (Nat × Nat × Nat) := [(4337707008,106463012226954,106463396255122)]
theorem point_links_checked33064 : (cuts33064.take 1).map (fun c => (4337696769-1+2*2^10*c.k,106462983675212+c.lower,106463367703360+c.upper)) = pointBounds33064 := by
 decide +kernel
def cuts33065 : List PrefixCut := [⟨8,49315120,49315150⟩,
⟨64,386015481,386015727⟩]
theorem checked33065 : checkPrefixCuts (2^48) 4337827841 10 Manual.Count131072.C033065.packed 64 cuts33065 = true := by
 decide +kernel
def pointBounds33065 : List (Nat × Nat × Nat) := [(4337844224,106463416811211,106463800839641)]
theorem point_links_checked33065 : (cuts33065.take 1).map (fun c => (4337827841-1+2*2^10*c.k,106463367496091+c.lower,106463751524491+c.upper)) = pointBounds33065 := by
 decide +kernel
def cuts33066 : List PrefixCut := [⟨11,64886310,64886352⟩,
⟨64,380812961,380813204⟩]
theorem checked33066 : checkPrefixCuts (2^48) 4337958913 10 Manual.Count131072.C033066.packed 64 cuts33066 = true := by
 decide +kernel
def pointBounds33066 : List (Nat × Nat × Nat) := [(4337981440,106463818397882,106464202426570)]
theorem point_links_checked33066 : (cuts33066.take 1).map (fun c => (4337958913-1+2*2^10*c.k,106463753511572+c.lower,106464137540218+c.upper)) = pointBounds33066 := by
 decide +kernel
def cuts33067 : List PrefixCut := [⟨14,85517514,85517569⟩,
⟨64,386186880,386187128⟩]
theorem checked33067 : checkPrefixCuts (2^48) 4338089985 10 Manual.Count131072.C033067.packed 64 cuts33067 = true := by
 decide +kernel
def pointBounds33067 : List (Nat × Nat × Nat) := [(4338118656,106464219842047,106464603870991)]
theorem point_links_checked33067 : (cuts33067.take 1).map (fun c => (4338089985-1+2*2^10*c.k,106464134324533+c.lower,106464518353422+c.upper)) = pointBounds33067 := by
 decide +kernel
def cuts33068 : List PrefixCut := [⟨17,100956852,100956917⟩,
⟨64,384553121,384553364⟩]
theorem checked33068 : checkPrefixCuts (2^48) 4338221057 10 Manual.Count131072.C033068.packed 64 cuts33068 = true := by
 decide +kernel
def pointBounds33068 : List (Nat × Nat × Nat) := [(4338255872,106464621468265,106465005497467)]
theorem point_links_checked33068 : (cuts33068.take 1).map (fun c => (4338221057-1+2*2^10*c.k,106464520511413+c.lower,106464904540550+c.upper)) = pointBounds33068 := by
 decide +kernel
def cuts33069 : List PrefixCut := [⟨20,122948156,122948234⟩,
⟨64,382595152,382595399⟩]
theorem checked33069 : checkPrefixCuts (2^48) 4338352129 10 Manual.Count131072.C033069.packed 64 cuts33069 = true := by
 decide +kernel
def pointBounds33069 : List (Nat × Nat × Nat) := [(4338393088,106465028012690,106465412042148)]
theorem point_links_checked33069 : (cuts33069.take 1).map (fun c => (4338352129-1+2*2^10*c.k,106464905064534+c.lower,106465289093914+c.upper)) = pointBounds33069 := by
 decide +kernel
def cuts33070 : List PrefixCut := [⟨23,139293679,139293768⟩,
⟨64,387254745,387254990⟩]
theorem checked33070 : checkPrefixCuts (2^48) 4338483201 10 Manual.Count131072.C033070.packed 64 cuts33070 = true := by
 decide +kernel
def pointBounds33070 : List (Nat × Nat × Nat) := [(4338530304,106465426953365,106465810983081)]
theorem point_links_checked33070 : (cuts33070.take 1).map (fun c => (4338483201-1+2*2^10*c.k,106465287659686+c.lower,106465671689313+c.upper)) = pointBounds33070 := by
 decide +kernel
def cuts33071 : List PrefixCut := [⟨26,157843996,157844099⟩,
⟨64,388670325,388670572⟩]
theorem checked33071 : checkPrefixCuts (2^48) 4338614273 10 Manual.Count131072.C033071.packed 64 cuts33071 = true := by
 decide +kernel
def pointBounds33071 : List (Nat × Nat × Nat) := [(4338667520,106465832758427,106466216788402)]
theorem point_links_checked33071 : (cuts33071.take 1).map (fun c => (4338614273-1+2*2^10*c.k,106465674914431+c.lower,106466058944303+c.upper)) = pointBounds33071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000095
