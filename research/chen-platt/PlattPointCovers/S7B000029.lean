import PlattPointSubsetKernel
import PlattPointPackets.S2B000145
import PlattPointPackets.S2B000146
import PlattPointPackets.S2B000147
import PlattPointPackets.S2B000148
import PlattPointPackets.S2B000149
import PlattGlobalGrid.S7B000029
namespace ChenEffective.PlattWindow.PointCovers.S7B000029
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000145.points ++ ChenEffective.PlattWindow.PointPackets.S2B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000148.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000149.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000029.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000029.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000029
