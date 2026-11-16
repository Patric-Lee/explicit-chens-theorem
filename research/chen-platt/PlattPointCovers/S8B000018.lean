import PlattPointSubsetKernel
import PlattPointPackets.S4B000140
import PlattPointPackets.S4B000141
import PlattPointPackets.S4B000142
import PlattPointPackets.S4B000143
import PlattPointPackets.S4B000144
import PlattPointPackets.S4B000145
import PlattPointPackets.S4B000146
import PlattPointPackets.S4B000147
import PlattPointPackets.S4B000148
import PlattGlobalGrid.S8B000018
namespace ChenEffective.PlattWindow.PointCovers.S8B000018
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000140.points ++ ChenEffective.PlattWindow.PointPackets.S4B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000148.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000018.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000018.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000018
