import PlattPointSubsetKernel
import PlattPointPackets.S2B000176
import PlattPointPackets.S2B000177
import PlattPointPackets.S2B000178
import PlattPointPackets.S2B000179
import PlattPointPackets.S2B000180
import PlattGlobalGrid.S7B000037
namespace ChenEffective.PlattWindow.PointCovers.S7B000037
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000176.points ++ ChenEffective.PlattWindow.PointPackets.S2B000177.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000178.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000179.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000180.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000037.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000037.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000037
