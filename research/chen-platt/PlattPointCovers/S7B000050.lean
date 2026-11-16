import PlattPointSubsetKernel
import PlattPointPackets.S2B000230
import PlattPointPackets.S2B000231
import PlattPointPackets.S2B000232
import PlattPointPackets.S2B000233
import PlattPointPackets.S2B000234
import PlattGlobalGrid.S7B000050
namespace ChenEffective.PlattWindow.PointCovers.S7B000050
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000230.points ++ ChenEffective.PlattWindow.PointPackets.S2B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000234.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000050.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000050.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000050
