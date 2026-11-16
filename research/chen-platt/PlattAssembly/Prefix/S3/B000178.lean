import PlattAssemblyKernel
import PlattCertificates.Count131072.C025696
import PlattCertificates.Count131072.C025697
import PlattCertificates.Count131072.C025698
import PlattCertificates.Count131072.C025699
import PlattCertificates.Count131072.C025700
import PlattCertificates.Count131072.C025701
import PlattCertificates.Count131072.C025702
import PlattCertificates.Count131072.C025703
import PlattCertificates.Count131072.C025704
import PlattCertificates.Count131072.C025705
import PlattCertificates.Count131072.C025706
import PlattCertificates.Count131072.C025707
import PlattCertificates.Count131072.C025708
import PlattCertificates.Count131072.C025709
import PlattCertificates.Count131072.C025710
import PlattCertificates.Count131072.C025711
import PlattCertificates.Count131072.C025712
import PlattCertificates.Count131072.C025713
import PlattCertificates.Count131072.C025714
import PlattCertificates.Count131072.C025715
import PlattCertificates.Count131072.C025716
import PlattCertificates.Count131072.C025717
import PlattCertificates.Count131072.C025718
import PlattCertificates.Count131072.C025719
import PlattCertificates.Count131072.C025720
import PlattCertificates.Count131072.C025721
import PlattCertificates.Count131072.C025722
import PlattCertificates.Count131072.C025723
import PlattCertificates.Count131072.C025724
import PlattCertificates.Count131072.C025725
import PlattCertificates.Count131072.C025726
import PlattCertificates.Count131072.C025727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000178
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25696 : List PrefixCut := [⟨20,79050777,79050821⟩,
⟨123,478637896,478638165⟩,
⟨128,497335629,497335911⟩]
theorem checked25696 : checkPrefixCuts (2^48) 3371958273 9 Manual.Count131072.C025696.packed 128 cuts25696 = true := by
 decide +kernel
def pointBounds25696 : List (Nat × Nat × Nat) := [(3371978752,103250175551035,103250557764868),(3372084224,103250575138154,103250957352212)]
theorem point_links_checked25696 : (cuts25696.take 2).map (fun c => (3371958273-1+2*2^9*c.k,103250096500258+c.lower,103250478714047+c.upper)) = pointBounds25696 := by
 decide +kernel
def cuts25697 : List PrefixCut := [⟨98,384215730,384215950⟩,
⟨128,497566754,497567037⟩]
theorem checked25697 : checkPrefixCuts (2^48) 3372089345 9 Manual.Count131072.C025697.packed 128 cuts25697 = true := by
 decide +kernel
def pointBounds25697 : List (Nat × Nat × Nat) := [(3372189696,103250978051617,103251360265908)]
theorem point_links_checked25697 : (cuts25697.take 1).map (fun c => (3372089345-1+2*2^9*c.k,103250593835887+c.lower,103250976049958+c.upper)) = pointBounds25697 := by
 decide +kernel
def cuts25698 : List PrefixCut := [⟨73,282037671,282037822⟩,
⟨128,495794511,495794781⟩]
theorem checked25698 : checkPrefixCuts (2^48) 3372220417 9 Manual.Count131072.C025698.packed 128 cuts25698 = true := by
 decide +kernel
def pointBounds25698 : List (Nat × Nat × Nat) := [(3372295168,103251373440312,103251755654817)]
theorem point_links_checked25698 : (cuts25698.take 1).map (fun c => (3372220417-1+2*2^9*c.k,103251091402641+c.lower,103251473616995+c.upper)) = pointBounds25698 := by
 decide +kernel
def cuts25699 : List PrefixCut := [⟨48,187462060,187462161⟩,
⟨128,501701191,501701468⟩]
theorem checked25699 : checkPrefixCuts (2^48) 3372351489 9 Manual.Count131072.C025699.packed 128 cuts25699 = true := by
 decide +kernel
def pointBounds25699 : List (Nat × Nat × Nat) := [(3372400640,103251774659212,103252156873937)]
theorem point_links_checked25699 : (cuts25699.take 1).map (fun c => (3372351489-1+2*2^9*c.k,103251587197152+c.lower,103251969411776+c.upper)) = pointBounds25699 := by
 decide +kernel
def cuts25700 : List PrefixCut := [⟨23,87301186,87301235⟩,
⟨126,491833400,491833669⟩,
⟨128,499845465,499845738⟩]
theorem checked25700 : checkPrefixCuts (2^48) 3372482561 9 Manual.Count131072.C025700.packed 128 cuts25700 = true := by
 decide +kernel
def pointBounds25700 : List (Nat × Nat × Nat) := [(3372506112,103252176199529,103252558414479),(3372611584,103252580731743,103252962946913)]
theorem point_links_checked25700 : (cuts25700.take 2).map (fun c => (3372482561-1+2*2^9*c.k,103252088898343+c.lower,103252471113244+c.upper)) = pointBounds25700 := by
 decide +kernel
def cuts25701 : List PrefixCut := [⟨101,395506066,395506286⟩,
⟨128,499826167,499826448⟩]
theorem checked25701 : checkPrefixCuts (2^48) 3372613633 9 Manual.Count131072.C025701.packed 128 cuts25701 = true := by
 decide +kernel
def pointBounds25701 : List (Nat × Nat × Nat) := [(3372717056,103252984249874,103253366465268)]
theorem point_links_checked25701 : (cuts25701.take 1).map (fun c => (3372613633-1+2*2^9*c.k,103252588743808+c.lower,103252970958982+c.upper)) = pointBounds25701 := by
 decide +kernel
def cuts25702 : List PrefixCut := [⟨76,298350811,298350978⟩,
⟨128,502226865,502227141⟩]
theorem checked25702 : checkPrefixCuts (2^48) 3372744705 9 Manual.Count131072.C025702.packed 128 cuts25702 = true := by
 decide +kernel
def pointBounds25702 : List (Nat × Nat × Nat) := [(3372822528,103253386920786,103253769136408)]
theorem point_links_checked25702 : (cuts25702.take 1).map (fun c => (3372744705-1+2*2^9*c.k,103253088569975+c.lower,103253470785430+c.upper)) = pointBounds25702 := by
 decide +kernel
def cuts25703 : List PrefixCut := [⟨51,197196699,197196813⟩,
⟨128,495531276,495531561⟩]
theorem checked25703 : checkPrefixCuts (2^48) 3372875777 9 Manual.Count131072.C025703.packed 128 cuts25703 = true := by
 decide +kernel
def pointBounds25703 : List (Nat × Nat × Nat) := [(3372928000,103253787993539,103254170209384)]
theorem point_links_checked25703 : (cuts25703.take 1).map (fun c => (3372875777-1+2*2^9*c.k,103253590796840+c.lower,103253973012571+c.upper)) = pointBounds25703 := by
 decide +kernel
def cuts25704 : List PrefixCut := [⟨26,103560116,103560172⟩,
⟨128,503439537,503439820⟩]
theorem checked25704 : checkPrefixCuts (2^48) 3373006849 9 Manual.Count131072.C025704.packed 128 cuts25704 = true := by
 decide +kernel
def pointBounds25704 : List (Nat × Nat × Nat) := [(3373033472,103254189888232,103254572104304)]
theorem point_links_checked25704 : (cuts25704.take 1).map (fun c => (3373006849-1+2*2^9*c.k,103254086328116+c.lower,103254468544132+c.upper)) = pointBounds25704 := by
 decide +kernel
def cuts25705 : List PrefixCut := [⟨1,4088854,4088856⟩,
⟨104,405374359,405374585⟩,
⟨128,502668986,502669262⟩]
theorem checked25705 : checkPrefixCuts (2^48) 3373137921 9 Manual.Count131072.C025705.packed 128 cuts25705 = true := by
 decide +kernel
def pointBounds25705 : List (Nat × Nat × Nat) := [(3373138944,103254593856507,103254976072808),(3373244416,103254995142012,103255377358537)]
theorem point_links_checked25705 : (cuts25705.take 2).map (fun c => (3373137921-1+2*2^9*c.k,103254589767653+c.lower,103254971983952+c.upper)) = pointBounds25705 := by
 decide +kernel
def cuts25706 : List PrefixCut := [⟨79,312823153,312823324⟩,
⟨128,500229718,500229992⟩]
theorem checked25706 : checkPrefixCuts (2^48) 3373268993 9 Manual.Count131072.C025706.packed 128 cuts25706 = true := by
 decide +kernel
def pointBounds25706 : List (Nat × Nat × Nat) := [(3373349888,103255405259792,103255787476538)]
theorem point_links_checked25706 : (cuts25706.take 1).map (fun c => (3373268993-1+2*2^9*c.k,103255092436639+c.lower,103255474653214+c.upper)) = pointBounds25706 := by
 decide +kernel
def cuts25707 : List PrefixCut := [⟨54,210933385,210933500⟩,
⟨128,496288683,496288956⟩]
theorem checked25707 : checkPrefixCuts (2^48) 3373400065 9 Manual.Count131072.C025707.packed 128 cuts25707 = true := by
 decide +kernel
def pointBounds25707 : List (Nat × Nat × Nat) := [(3373455360,103255803599742,103256185816706)]
theorem point_links_checked25707 : (cuts25707.take 1).map (fun c => (3373400065-1+2*2^9*c.k,103255592666357+c.lower,103255974883206+c.upper)) = pointBounds25707 := by
 decide +kernel
def cuts25708 : List PrefixCut := [⟨29,114807830,114807895⟩,
⟨128,508200513,508200802⟩]
theorem checked25708 : checkPrefixCuts (2^48) 3373531137 9 Manual.Count131072.C025708.packed 128 cuts25708 = true := by
 decide +kernel
def pointBounds25708 : List (Nat × Nat × Nat) := [(3373560832,103256203762870,103256585980057)]
theorem point_links_checked25708 : (cuts25708.take 1).map (fun c => (3373531137-1+2*2^9*c.k,103256088955040+c.lower,103256471172162+c.upper)) = pointBounds25708 := by
 decide +kernel
def cuts25709 : List PrefixCut := [⟨4,16936897,16936905⟩,
⟨107,417825847,417826079⟩,
⟨128,500421614,500421894⟩]
theorem checked25709 : checkPrefixCuts (2^48) 3373662209 9 Manual.Count131072.C025709.packed 128 cuts25709 = true := by
 decide +kernel
def pointBounds25709 : List (Nat × Nat × Nat) := [(3373666304,103256614092450,103256996309869),(3373771776,103257014981400,103257397199043)]
theorem point_links_checked25709 : (cuts25709.take 2).map (fun c => (3373662209-1+2*2^9*c.k,103256597155553+c.lower,103256979372964+c.upper)) = pointBounds25709 := by
 decide +kernel
def cuts25710 : List PrefixCut := [⟨82,314693303,314693480⟩,
⟨128,495313081,495313360⟩]
theorem checked25710 : checkPrefixCuts (2^48) 3373793281 9 Manual.Count131072.C025710.packed 128 cuts25710 = true := by
 decide +kernel
def pointBounds25710 : List (Nat × Nat × Nat) := [(3373877248,103257412270470,103257794488338)]
theorem point_links_checked25710 : (cuts25710.take 1).map (fun c => (3373793281-1+2*2^9*c.k,103257097577167+c.lower,103257479794858+c.upper)) = pointBounds25710 := by
 decide +kernel
def cuts25711 : List PrefixCut := [⟨57,221662433,221662558⟩,
⟨128,500382741,500383022⟩]
theorem checked25711 : checkPrefixCuts (2^48) 3373924353 9 Manual.Count131072.C025711.packed 128 cuts25711 = true := by
 decide +kernel
def pointBounds25711 : List (Nat × Nat × Nat) := [(3373982720,103257814552681,103258196770776)]
theorem point_links_checked25711 : (cuts25711.take 1).map (fun c => (3373924353-1+2*2^9*c.k,103257592890248+c.lower,103257975108218+c.upper)) = pointBounds25711 := by
 decide +kernel
def cuts25712 : List PrefixCut := [⟨32,124049892,124049960⟩,
⟨128,492188116,492188390⟩]
theorem checked25712 : checkPrefixCuts (2^48) 3374055425 9 Manual.Count131072.C025712.packed 128 cuts25712 = true := by
 decide +kernel
def pointBounds25712 : List (Nat × Nat × Nat) := [(3374088192,103258217322881,103258599541200)]
theorem point_links_checked25712 : (cuts25712.take 1).map (fun c => (3374055425-1+2*2^9*c.k,103258093272989+c.lower,103258475491240+c.upper)) = pointBounds25712 := by
 decide +kernel
def cuts25713 : List PrefixCut := [⟨7,27862276,27862291⟩,
⟨110,422515588,422515830⟩,
⟨128,492168832,492169112⟩]
theorem checked25713 : checkPrefixCuts (2^48) 3374186497 9 Manual.Count131072.C025713.packed 128 cuts25713 = true := by
 decide +kernel
def pointBounds25713 : List (Nat × Nat × Nat) := [(3374193664,103258613323381,103258995541921),(3374299136,103259007976693,103259390195460)]
theorem point_links_checked25713 : (cuts25713.take 2).map (fun c => (3374186497-1+2*2^9*c.k,103258585461105+c.lower,103258967679630+c.upper)) = pointBounds25713 := by
 decide +kernel
def cuts25714 : List PrefixCut := [⟨85,323736587,323736770⟩,
⟨128,492733643,492733919⟩]
theorem checked25714 : checkPrefixCuts (2^48) 3374317569 9 Manual.Count131072.C025714.packed 128 cuts25714 = true := by
 decide +kernel
def pointBounds25714 : List (Nat × Nat × Nat) := [(3374404608,103259401366524,103259783585512)]
theorem point_links_checked25714 : (cuts25714.take 1).map (fun c => (3374317569-1+2*2^9*c.k,103259077629937+c.lower,103259459848742+c.upper)) = pointBounds25714 := by
 decide +kernel
def cuts25715 : List PrefixCut := [⟨60,230052577,230052708⟩,
⟨128,497135263,497135542⟩]
theorem checked25715 : checkPrefixCuts (2^48) 3374448641 9 Manual.Count131072.C025715.packed 128 cuts25715 = true := by
 decide +kernel
def pointBounds25715 : List (Nat × Nat × Nat) := [(3374510080,103259800416157,103260182635369)]
theorem point_links_checked25715 : (cuts25715.take 1).map (fun c => (3374448641-1+2*2^9*c.k,103259570363580+c.lower,103259952582661+c.upper)) = pointBounds25715 := by
 decide +kernel
def cuts25716 : List PrefixCut := [⟨35,133038805,133038881⟩,
⟨128,491277452,491277728⟩]
theorem checked25716 : checkPrefixCuts (2^48) 3374579713 9 Manual.Count131072.C025716.packed 128 cuts25716 = true := by
 decide +kernel
def pointBounds25716 : List (Nat × Nat × Nat) := [(3374615552,103260200537648,103260582757084)]
theorem point_links_checked25716 : (cuts25716.take 1).map (fun c => (3374579713-1+2*2^9*c.k,103260067498843+c.lower,103260449718203+c.upper)) = pointBounds25716 := by
 decide +kernel
def cuts25717 : List PrefixCut := [⟨10,40035354,40035377⟩,
⟨113,435294340,435294588⟩,
⟨128,491341876,491342156⟩]
theorem checked25717 : checkPrefixCuts (2^48) 3374710785 9 Manual.Count131072.C025717.packed 128 cuts25717 = true := by
 decide +kernel
def pointBounds25717 : List (Nat × Nat × Nat) := [(3374721024,103260598811649,103260981031308),(3374826496,103260994070635,103261376290519)]
theorem point_links_checked25717 : (cuts25717.take 2).map (fun c => (3374710785-1+2*2^9*c.k,103260558776295+c.lower,103260940995931+c.upper)) = pointBounds25717 := by
 decide +kernel
def cuts25718 : List PrefixCut := [⟨88,343118913,343119105⟩,
⟨128,496410209,496410487⟩]
theorem checked25718 : checkPrefixCuts (2^48) 3374841857 9 Manual.Count131072.C025718.packed 128 cuts25718 = true := by
 decide +kernel
def pointBounds25718 : List (Nat × Nat × Nat) := [(3374931968,103261393237084,103261775457192)]
theorem point_links_checked25718 : (cuts25718.take 1).map (fun c => (3374841857-1+2*2^9*c.k,103261050118171+c.lower,103261432338087+c.upper)) = pointBounds25718 := by
 decide +kernel
def cuts25719 : List PrefixCut := [⟨63,247447318,247447454⟩,
⟨128,498225781,498226055⟩]
theorem checked25719 : checkPrefixCuts (2^48) 3374972929 9 Manual.Count131072.C025719.packed 128 cuts25719 = true := by
 decide +kernel
def pointBounds25719 : List (Nat × Nat × Nat) := [(3375037440,103261793975698,103262176196028)]
theorem point_links_checked25719 : (cuts25719.take 1).map (fun c => (3374972929-1+2*2^9*c.k,103261546528380+c.lower,103261928748574+c.upper)) = pointBounds25719 := by
 decide +kernel
def cuts25720 : List PrefixCut := [⟨38,147779358,147779441⟩,
⟨128,504711253,504711532⟩]
theorem checked25720 : checkPrefixCuts (2^48) 3375104001 9 Manual.Count131072.C025720.packed 128 cuts25720 = true := by
 decide +kernel
def pointBounds25720 : List (Nat × Nat × Nat) := [(3375142912,103262192533519,103262574754070)]
theorem point_links_checked25720 : (cuts25720.take 1).map (fun c => (3375104001-1+2*2^9*c.k,103262044754161+c.lower,103262426974629+c.upper)) = pointBounds25720 := by
 decide +kernel
def cuts25721 : List PrefixCut := [⟨14,55206820,55206851⟩,
⟨118,458409539,458409796⟩,
⟨128,496102294,496102571⟩]
theorem checked25721 : checkPrefixCuts (2^48) 3375235073 9 Manual.Count131072.C025721.packed 128 cuts25721 = true := by
 decide +kernel
def pointBounds25721 : List (Nat × Nat × Nat) := [(3375249408,103262604672234,103262986893012),(3375355904,103263007874953,103263390095957)]
theorem point_links_checked25721 : (cuts25721.take 2).map (fun c => (3375235073-1+2*2^9*c.k,103262549465414+c.lower,103262931686161+c.upper)) = pointBounds25721 := by
 decide +kernel
def cuts25722 : List PrefixCut := [⟨94,371751383,371751592⟩,
⟨128,503254449,503254730⟩]
theorem checked25722 : checkPrefixCuts (2^48) 3375366145 9 Manual.Count131072.C025722.packed 128 cuts25722 = true := by
 decide +kernel
def pointBounds25722 : List (Nat × Nat × Nat) := [(3375462400,103263417319091,103263799540324)]
theorem point_links_checked25722 : (cuts25722.take 1).map (fun c => (3375366145-1+2*2^9*c.k,103263045567708+c.lower,103263427788732+c.upper)) = pointBounds25722 := by
 decide +kernel
def cuts25723 : List PrefixCut := [⟨70,273592095,273592247⟩,
⟨128,501233618,501233898⟩]
theorem checked25723 : checkPrefixCuts (2^48) 3375497217 9 Manual.Count131072.C025723.packed 128 cuts25723 = true := by
 decide +kernel
def pointBounds25723 : List (Nat × Nat × Nat) := [(3375568896,103263822414252,103264204635709)]
theorem point_links_checked25723 : (cuts25723.take 1).map (fun c => (3375497217-1+2*2^9*c.k,103263548822157+c.lower,103263931043462+c.upper)) = pointBounds25723 := by
 decide +kernel
def cuts25724 : List PrefixCut := [⟨46,179108543,179108646⟩,
⟨128,499046241,499046521⟩]
theorem checked25724 : checkPrefixCuts (2^48) 3375628289 9 Manual.Count131072.C025724.packed 128 cuts25724 = true := by
 decide +kernel
def pointBounds25724 : List (Nat × Nat × Nat) := [(3375675392,103264229164318,103264611386006)]
theorem point_links_checked25724 : (cuts25724.take 1).map (fun c => (3375628289-1+2*2^9*c.k,103264050055775+c.lower,103264432277360+c.upper)) = pointBounds25724 := by
 decide +kernel
def cuts25725 : List PrefixCut := [⟨22,84464879,84464925⟩,
⟨126,488521157,488521434⟩,
⟨128,496442067,496442348⟩]
theorem checked25725 : checkPrefixCuts (2^48) 3375759361 9 Manual.Count131072.C025725.packed 128 cuts25725 = true := by
 decide +kernel
def pointBounds25725 : List (Nat × Nat × Nat) := [(3375781888,103264633566895,103265015788806),(3375888384,103265037623173,103265419845315)]
theorem point_links_checked25725 : (cuts25725.take 2).map (fun c => (3375759361-1+2*2^9*c.k,103264549102016+c.lower,103264931323881+c.upper)) = pointBounds25725 := by
 decide +kernel
def cuts25726 : List PrefixCut := [⟨102,400208071,400208294⟩,
⟨128,501758902,501759179⟩]
theorem checked25726 : checkPrefixCuts (2^48) 3375890433 9 Manual.Count131072.C025726.packed 128 cuts25726 = true := by
 decide +kernel
def pointBounds25726 : List (Nat × Nat × Nat) := [(3375994880,103265445752154,103265827974523)]
theorem point_links_checked25726 : (cuts25726.take 1).map (fun c => (3375890433-1+2*2^9*c.k,103265045544083+c.lower,103265427766229+c.upper)) = pointBounds25726 := by
 decide +kernel
def cuts25727 : List PrefixCut := [⟨78,304814453,304814629⟩,
⟨128,498821389,498821676⟩]
theorem checked25727 : checkPrefixCuts (2^48) 3376021505 9 Manual.Count131072.C025727.packed 128 cuts25727 = true := by
 decide +kernel
def pointBounds25727 : List (Nat × Nat × Nat) := [(3376101376,103265852117438,103266234340037)]
theorem point_links_checked25727 : (cuts25727.take 1).map (fun c => (3376021505-1+2*2^9*c.k,103265547302985+c.lower,103265929525408+c.upper)) = pointBounds25727 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000178
